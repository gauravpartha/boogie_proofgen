using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Isabelle.Ast;
using Microsoft.Boogie;
using Microsoft.Boogie.GraphUtil;
using Microsoft.Boogie.ProofGen;
using Microsoft.Boogie.TypeErasure;
using Microsoft.Boogie.VCExprAST;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.BoogieIsaInterface.VariableTranslation;
using ProofGeneration.CFGRepresentation;
using ProofGeneration.CfgToDag;
using ProofGeneration.Passification;
using ProofGeneration.ProgramToVCProof;
using ProofGeneration.Util;
using ProofGeneration.VCProofGen;

namespace ProofGeneration
{
    public class ProofGenerationLayer
    {
        private static Implementation afterPassificationImpl;

        private static IDictionary<Block, Block> beforeDagOrigBlock;
        private static IDictionary<Block, Block> beforeDagAfterDagBlock;
        private static CFGRepr beforeDagCfg;

        private static BoogieMethodData beforeDagData;

        private static IDictionary<Block, Block> beforePassiveToAfterPassiveBlock;
        private static IDictionary<Block, Block> beforePassiveOrigBlock;
        private static CFGRepr beforePassificationCfg;

        private static BoogieMethodData beforePassiveData;

        private static IDictionary<Block, Block> afterPassificationToOrigBlock;
        private static CFGRepr afterPassificationCfg;
        private static CFGRepr noEmptyBlocksCfg;
        private static IDictionary<Block, Block> afterPassificationToAfterUnreachableBlock;
        private static CFGRepr afterUnreachablePruningCfg;

        private static BoogieMethodData finalProgData;
        private static IVariableTranslationFactory varTranslationFactory;

        private static BoogieGlobalData boogieGlobalData;

        private static IDictionary<Block, IDictionary<Variable, Expr>> initialVarMapping;

        //VC Automation Hints
        private static VCHintManager vcHintManager;
        private static TypePremiseEraserFactory typePremiseEraserFactory;

        //Passification Automation Hints
        private static PassificationHintManager passificationHintManager;

        private static PassiveRelationGen passiveRelationGen;
        private static IDictionary<Variable, int> globalVersionMap;

        private static CfgToDagHintManager cfgToDagHintManager;

        private static Block uniqueExitBlockOrig;

        private static readonly ProofGenConfig _proofGenConfig =
            new ProofGenConfig(true, true, true);

        private static IProgramAccessor globalDataProgAccess;

        private static IDictionary<string, IProgramAccessor> procNameToTopLevelPrograms = new Dictionary<string, IProgramAccessor>();
        
        /// <summary>
        /// Provide program for the next procedure (for the global declarations).
        /// </summary>
        public static void Program(Program p)
        {
            if (boogieGlobalData == null)
            {
                boogieGlobalData = new BoogieGlobalData(p.Functions, p.Axioms, p.GlobalVariables, p.Constants);
                
                var methodData = BoogieMethodData.CreateOnlyGlobal(boogieGlobalData);
                var fixedVarTranslation = new DeBruijnFixedVarTranslation(methodData);
                var fixedTyVarTranslation = new DeBruijnFixedTVarTranslation(methodData);
                var factory =
                    new DeBruijnVarFactory(fixedVarTranslation, fixedTyVarTranslation, boogieGlobalData);
                var globalDataTheoryName = "global_data";
                var globalDataConfig = new IsaProgramGeneratorConfig(null, true, true, true, false, SpecsConfig.None, false);
                globalDataProgAccess = new IsaProgramGenerator().GetIsaProgram(
                    globalDataTheoryName,
                    "proc",
                    methodData, globalDataConfig, factory, 
                    null,
                    out var declsGlobalData,
                    !CommandLineOptions.Clo.GenerateIsaProgNoProofs,
                    true
                );
                
                var globalDataTheory = new Theory(globalDataTheoryName,
                    new List<string> {"Boogie_Lang.Semantics", "Boogie_Lang.TypeSafety", "Boogie_Lang.Util"},
                    declsGlobalData);
                ProofGenerationOutput.StoreTheoriesTopLevel(new List<Theory> { globalDataTheory });
            }
        }

        /// <summary>
        /// Provide source CFG for CFG-to-DAG phase
        /// </summary>
        public static void BeforeCFGToDAG(Implementation impl)
        {
            var config = new CFGReprConfigBuilder().SetIsAcyclic(false).SetBlockCopy(true).SetDesugarCalls(true)
                .Build();
            beforeDagCfg = CFGReprTransformer.GetCfgRepresentation(impl,
                config,
                out beforeDagOrigBlock,
                out var newVarsFromDesugaring);
            beforeDagData = MethodDataFromImpl(impl, boogieGlobalData, newVarsFromDesugaring);
            uniqueExitBlockOrig = null;
        }

        /// <summary>
        /// Provide graph for which all the loop information has been computed</param>
        /// </summary>
        public static void GraphCfgToDag(Graph<Block> g)
        {
            cfgToDagHintManager = new CfgToDagHintManager(g, beforeDagOrigBlock);
        }

        /// <summary>
        /// Provide the generated unified exit block. If no unified exit block is created (for example, when there is only
        /// one exit block), then invoke this method with null.
        /// </summary>
        public static void CreateUnifiedExitBlock(Block generatedExitBlock)
        {
            uniqueExitBlockOrig = generatedExitBlock;
        }

        
        /// <summary>
        /// Provide source CFG for passification phase
        /// </summary>
        public static void BeforePassification(Implementation impl)
        {
            if (CommandLineOptions.Clo.GenerateIsaProgNoProofs)
                return;
            
            var config = new CFGReprConfigBuilder().SetIsAcyclic(true).SetBlockCopy(true).SetDesugarCalls(true)
                .Build();
            beforePassificationCfg = CFGReprTransformer.GetCfgRepresentation(
                impl,
                config,
                out beforePassiveOrigBlock,
                out var newVarsFromDesugaring
            );
            cfgToDagHintManager.AfterDagToOrig = beforePassiveOrigBlock;
            beforePassiveData = MethodDataFromImpl(impl, boogieGlobalData, newVarsFromDesugaring);
            passificationHintManager = new PassificationHintManager(beforePassiveOrigBlock);
            initialVarMapping = new Dictionary<Block, IDictionary<Variable, Expr>>();

            // compute mapping between copied blocks (before dag -> after dag)
            var origToAfterDag = beforePassiveOrigBlock.InverseDict();

            beforeDagAfterDagBlock = DictionaryComposition(beforeDagOrigBlock, origToAfterDag);
        }

        private static BoogieMethodData MethodDataFromImpl(
            Implementation impl,
            BoogieGlobalData globalData,
            List<Variable> extraLocalVariables = null
        )
        {
            //add out params to local variables for now
            var locals = new List<Variable>(impl.LocVars).Union(impl.OutParams);
            if (extraLocalVariables != null)
                locals = locals.Union(extraLocalVariables);


            /* procedures and implementations do not use the same objects for the variables in the spec --> need to sync 
             * for pre- and postcondition
             */
            var formalProcImplSubst = Substituter.SubstitutionFromDictionary(impl.GetImplFormalMap());
            var preconditions = new List<Tuple<Expr,bool>>();
            foreach (var req in impl.Proc.Requires)
            {
                var e = Substituter.Apply(formalProcImplSubst, req.Condition);
                preconditions.Add(Tuple.Create(e, req.Free));
            }

            var postconditions = new List<Tuple<Expr,bool>>();
            foreach (var ens in impl.Proc.Ensures)
            {
                var e = Substituter.Apply(formalProcImplSubst, ens.Condition);
                postconditions.Add(Tuple.Create(e, ens.Free));
            }


            return new BoogieMethodData(
                globalData,
                new List<TypeVariable>(impl.TypeParameters),
                new List<Variable>(impl.InParams),
                locals,
                null,
                new List<IdentifierExpr>(impl.Proc.Modifies),
                preconditions,
                postconditions);
        }

        /// <summary>
        /// Provide variable relation <paramref name="variableToExpr"/>at the beginning of <paramref name="b"/>
        /// for the passification phase.
        /// </summary>
        public static void RecordInitialVariableMapping(Block b, IDictionary<Variable, Expr> variableToExpr)
        {
            Contract.Requires(b != null);
            Contract.Requires(variableToExpr != null);
            if (CommandLineOptions.Clo.GenerateIsaProgNoProofs)
                return;
            
            initialVarMapping.Add(b, new Dictionary<Variable, Expr>(variableToExpr));
        }

        /// <summary>
        ///     Returns whether the type checking phase before the VC generation may potentially rewrite <paramref name="cmd" />
        /// </summary>
        private static bool TypeCheckBeforeVcMaybeRewritesCmd(Cmd cmd)
        {
            /* Type checking phase rewrites boolean (in)equalities using "iff".
             * Only commands generated by the passification phase may be affected (i.e., assume commands with equalities),
             * since type checking is already executed once before the CFG-to-DAG phase.
             */
            if (cmd is AssumeCmd assumeCmd && assumeCmd.Expr is NAryExpr nAryExpr)
                return nAryExpr.Fun is BinaryOperator bop && bop.Op.Equals(BinaryOperator.Opcode.Eq);

            return false;
        }

        /// <summary>
        /// Provide target CFG for passification phase, construct global version map.
        /// </summary>
        /// <param name="impl">source CFG after passification phase</param>
        /// <exception cref="ProofGenUnexpectedStateException">thrown if global version map is incorrect
        ///  (should never happen). </exception>
        public static void AfterPassificationCheckGlobalMap(Implementation impl)
        {
            afterPassificationImpl = impl;
            
            if (CommandLineOptions.Clo.GenerateIsaProgNoProofs)
                return;
            
            finalProgData = MethodDataFromImpl(impl, boogieGlobalData);
            var config = new CFGReprConfigBuilder().SetIsAcyclic(true).SetBlockCopy(true).SetDesugarCalls(false)
                .SetDeepCopyPredCmd(TypeCheckBeforeVcMaybeRewritesCmd).Build();
            afterPassificationCfg =
                CFGReprTransformer.GetCfgRepresentation(impl, config, out afterPassificationToOrigBlock, out _);

            var passiveBlocks = new List<Block>(afterPassificationCfg.GetBlocksBackwards());

            var origToAfterPassificationBlock = afterPassificationToOrigBlock.InverseDict();

            beforePassiveToAfterPassiveBlock =
                DictionaryComposition(beforePassiveOrigBlock, origToAfterPassificationBlock);

            var globalVersion = new GlobalVersion();

            passiveRelationGen = new PassiveRelationGen(
                beforePassificationCfg,
                passificationHintManager,
                initialVarMapping,
                beforePassiveOrigBlock,
                beforePassiveToAfterPassiveBlock,
                ProofGenLiveVarAnalysis.ComputeLiveVariables(beforePassificationCfg, beforePassiveData)
            );

            //all variables before passification are the initial versions and already constrained
            globalVersionMap = globalVersion.GlobalVersionMap(
                passiveRelationGen,
                beforePassiveData.AllVariables(),
                afterPassificationCfg.entry,
                passiveBlocks);

            //Console.WriteLine("Version map: " + string.Join(Environment.NewLine, globalVersionMap));

            var versionMapCorrect =
                GlobalVersionChecker.CheckVersionMap(globalVersionMap, passiveRelationGen, beforePassificationCfg,
                    beforePassiveToAfterPassiveBlock);

            if (!versionMapCorrect)
                throw new ProofGenUnexpectedStateException(typeof(ProofGenerationLayer), "Incorrect version map");
        }

        /// <summary>
        ///     Compute composition of <paramref name="d1" /> and <paramref name="d2" />: if d1[k] is in domain of d2, then the
        ///     result
        ///     maps k to d2[d1[k]], and otherwise k is not in the domain of the result
        /// </summary>
        /// <param name="d1">Dictionary that must be injective</param>
        /// <param name="d2"></param>
        private static IDictionary<Block, Block> DictionaryComposition(IDictionary<Block, Block> d1,
            IDictionary<Block, Block> d2)
        {
            var result = new Dictionary<Block, Block>();
            foreach (var d1Elem in d1)
                if (d2.TryGetValue(d1Elem.Value, out var res))
                    result.Add(d1Elem.Key, res);

            return result;
        }

        /// <summary>
        /// Provide target CFG after unreachable blocks are pruned (after passification).
        /// </summary>
        public static void AfterUnreachablePruning(Implementation impl)
        {
            if (CommandLineOptions.Clo.GenerateIsaProgNoProofs)
                return;
            
            var config = new CFGReprConfigBuilder().SetIsAcyclic(true).SetBlockCopy(true).SetDesugarCalls(false)
                .SetDeepCopyPredCmd(TypeCheckBeforeVcMaybeRewritesCmd).Build();
            afterUnreachablePruningCfg =
                CFGReprTransformer.GetCfgRepresentation(impl, config, out var afterUnreachableToOrigBlock, out _);

            var origToAfterUnreachableBlock = afterUnreachableToOrigBlock.InverseDict();
            afterPassificationToAfterUnreachableBlock =
                DictionaryComposition(afterPassificationToOrigBlock, origToAfterUnreachableBlock);
        }

        /// <summary> Records hint for a cmd in the final passified Boogie program</summary>
        /// <param name="cmd">command</param>
        /// <param name="block">block containing command</param>
        /// <param name="exprVC">the computed VC for the expression in the command</param>
        /// <param name="postVC">the computed postcondition of the command</param>
        /// <param name="resultVC">Wlp(cmd, postVC)</param>
        /// <param name="subsumptionOption">The subsumption option for this cmd.</param>
        public static void NextVcHintForBlock(
            Cmd cmd,
            Block block,
            VCExpr exprVC,
            VCExpr postVC,
            VCExpr resultVC,
            CommandLineOptions.SubsumptionOption subsumptionOption
        )
        {
            if (CommandLineOptions.Clo.GenerateIsaProgNoProofs)
                return;
            vcHintManager.NextHintForBlock(cmd, block, exprVC, postVC, resultVC, subsumptionOption);
        }

        /// <summary>
        /// Provide a hint that passification of the non-passive command <paramref name="cmd"/> in block
        /// <paramref name="block"/> leads to non-passive variable <paramref name="origVar"/> being related to
        /// passive expression <paramref name="passiveExpr"/>
        /// </summary>
        public static void NextPassificationHint(Block block, Cmd cmd, Variable origVar, Expr passiveExpr)
        {
            if (CommandLineOptions.Clo.GenerateIsaProgNoProofs)
                return;
            passificationHintManager.AddHint(block, cmd, origVar, passiveExpr);
        }

        /// <summary>
        /// Provide hint that <paramref name="block"/> is a loop head of a loop with invariants <paramref name="invariants"/>
        /// and modified variables <paramref name="varsToHavoc"/>
        /// </summary>
        public static void LoopHeadHint(Block block, IEnumerable<Variable> varsToHavoc, IEnumerable<Expr> invariants)
        {
            if (CommandLineOptions.Clo.GenerateIsaProgNoProofs)
                return;
            cfgToDagHintManager.AddHint(block, new LoopHeadHint(varsToHavoc, invariants));
        }

        /// <summary>
        /// Provide hint that the backedge block <paramref name="oldBackedgeBlock"/> is replaced by a new backedge block
        /// <paramref name="newBackedgeBlock"/> for a loop with loop head <paramref name="loopHead"/>.
        /// </summary>
        public static void NewBackedgeBlock(Block oldBackedgeBlock, Block newBackedgeBlock, Block loopHead)
        {
            if (CommandLineOptions.Clo.GenerateIsaProgNoProofs)
                return;
            cfgToDagHintManager.AddNewBackedgeBlock(newBackedgeBlock, loopHead);
        }

        public static void SetTypeEraserFactory(TypePremiseEraserFactory factory)
        {
            if (CommandLineOptions.Clo.GenerateIsaProgNoProofs)
                return;
            typePremiseEraserFactory = factory;
            var uniqueNamer = new IsaUniqueNamer();
            /* Hack: try to make sure unique namer uses names for Boogie functions and Boogie variables that are different
             * from the default name otherwise it clashes with the functions potentially fixed in the context of a locale
             */
            foreach (var fun in boogieGlobalData.Functions) uniqueNamer.GetName(fun.Name, "o123_" + fun.Name);

            foreach (var variable in finalProgData.AllVariables())
                uniqueNamer.GetName(variable.Name, "o123_" + variable.Name);

            //Hack: translate vc variable based on name, to ensure that applying erasure multiple times shares the same variables
            var translator = VCExprToIsaTranslator.CreateNameBasedTranslator(uniqueNamer);
            translator.SetFunctionNamer(uniqueNamer);
            translator.SetTryInstantiatingFunctions(true);
            vcHintManager = new VCHintManager(new VcRewriteLemmaGen(factory, translator));
        }

        /// <summary>
        /// Generate all proofs for the current procedure. 
        /// </summary>
        /// <param name="vc">WP of the procedure body</param>
        /// <param name="vcAxioms">VC assumptions for the Boogie axioms</param>
        /// <param name="typeAxioms">VC assumptions for the Boogie type encoding</param>
        /// <param name="typeAxiomInfo">Hints about the type encoding</param>
        /// <param name="gen"></param>
        /// <param name="translator"></param>
        /// <param name="axiomBuilder"></param>
        /// <exception cref="ArgumentException">
        /// axiom builder must be null iff types are not erased (since no polymorphism in vc), otherwise exception is
        /// thrown
        /// </exception>
        public static void VCGenerateAllProofs(
            VCExpr vc,
            VCExpr vcAxioms,
            VCExpr typeAxioms,
            List<VCAxiomInfo> typeAxiomInfo,
            VCExpressionGenerator gen,
            Boogie2VCExprTranslator translator,
            TypeAxiomBuilderPremisses axiomBuilder)
        {
            var uniqueNamer = new IsaUniqueNamer();
            var theories = new List<Theory>();
            if (axiomBuilder == null && typeAxioms != null)
                throw new ArgumentException("type axioms can only be null if axiom builder is null");

            /* Since in the proofs calls are desugared, there can be more variables in "beforePassiveData". If only
             the progam should be generaed, then these variables should be ignored. */
            var mainData = CommandLineOptions.Clo.GenerateIsaProgNoProofs ? beforeDagData : beforePassiveData;
            
            var fixedVarTranslation2 = new DeBruijnFixedVarTranslation(mainData);
            var fixedTyVarTranslation2 = new DeBruijnFixedTVarTranslation(mainData);
            var varTranslationFactory2 =
                new DeBruijnVarFactory(fixedVarTranslation2, fixedTyVarTranslation2, boogieGlobalData);
            
            #region before cfg to dag program
            var beforeCfgToDagTheoryName = uniqueNamer.GetName(afterPassificationImpl.Name + "_before_cfg_to_dag_prog");
            //Hack: specs config used to distinguish between all (free + checks) (--> expression tuples) or just checked (no tuples)
            var specsConfig = CommandLineOptions.Clo.GenerateIsaProgNoProofs ? SpecsConfig.All : SpecsConfig.AllPreCheckedPost;
            var beforeCfgToDagConfig = new IsaProgramGeneratorConfig(globalDataProgAccess, false, false, false, true, specsConfig, true);
            var beforeCfgToDagProgAccess = new IsaProgramGenerator().GetIsaProgram(
                beforeCfgToDagTheoryName,
                afterPassificationImpl.Name,
                mainData, beforeCfgToDagConfig, varTranslationFactory2,
                beforeDagCfg,
                out var programDeclsBeforeCfgToDag,
                !CommandLineOptions.Clo.GenerateIsaProgNoProofs);
            procNameToTopLevelPrograms.Add(afterPassificationImpl.Proc.Name, beforeCfgToDagProgAccess);
            
            var beforeCfgToDagProgTheory = new Theory(beforeCfgToDagTheoryName,
                new List<string> {"Boogie_Lang.Semantics", "Boogie_Lang.TypeSafety", "Boogie_Lang.Util", "\"../"+globalDataProgAccess.TheoryName()+"\""},
                programDeclsBeforeCfgToDag);
            theories.Add(beforeCfgToDagProgTheory);
            #endregion

            if (CommandLineOptions.Clo.GenerateIsaProgNoProofs)
            {
                StoreResult("program_" + afterPassificationImpl.Proc.Name, theories);
                return;
            }

            #region before passive program

            var beforePassiveProgTheoryName = uniqueNamer.GetName(afterPassificationImpl.Name + "_before_passive_prog");
            var beforePassiveConfig =
                new IsaProgramGeneratorConfig(beforeCfgToDagProgAccess, false, false, false, false, SpecsConfig.None, false);
            var beforePassiveProgAccess = new IsaProgramGenerator().GetIsaProgram(beforePassiveProgTheoryName,
                afterPassificationImpl.Name,
                mainData, beforePassiveConfig, varTranslationFactory2,
                beforePassificationCfg,
                out var programDeclsBeforePassive,
                !CommandLineOptions.Clo.GenerateIsaProgNoProofs);

            #endregion

            var vcAllAxioms = AxiomHandler.AxiomInfo(
                axiomBuilder != null,
                boogieGlobalData.Axioms,
                vcAxioms,
                typeAxioms,
                typeAxiomInfo,
                out var allAxiomsInfo);

            var vcLocale = VCToIsaInterface.ConvertVC(
                "vc",
                vc,
                vcAllAxioms,
                new StandardActiveDecl(),
                translator,
                axiomBuilder,
                finalProgData,
                afterUnreachablePruningCfg,
                out var vcinst,
                out var vcinstAxiom,
                out var vcTranslator,
                out var vcFunctions);

            //use global version map for translation 
            var fixedVarTranslation = new SimpleFixedVarTranslation(globalVersionMap);
            var fixedTyVarTranslation = new DeBruijnFixedTVarTranslation(finalProgData);
            varTranslationFactory =
                new DeBruijnVarFactory(fixedVarTranslation, fixedTyVarTranslation, boogieGlobalData);

            var finalProgTheoryName = uniqueNamer.GetName(afterPassificationImpl.Name + "_passive_prog");
            var passiveProgConfig =
                new IsaProgramGeneratorConfig(beforePassiveProgAccess, false, false, false, true, SpecsConfig.None, false);
            var passiveProgAccess = new IsaProgramGenerator().GetIsaProgram(finalProgTheoryName,
                afterPassificationImpl.Name,
                finalProgData, passiveProgConfig, varTranslationFactory,
                //we use the CFG before the peep-hole transformations, so that we can directly use the VC to program proof in the passification phase
                afterPassificationCfg,
                out var programDecls,
                !CommandLineOptions.Clo.GenerateIsaProgNoProofs);

            var finalProgTheory =
                new Theory(finalProgTheoryName,
                    new List<string>
                        {"Boogie_Lang.Semantics", "Boogie_Lang.Util", beforePassiveProgAccess.TheoryName()},
                    programDecls);
            theories.Add(finalProgTheory);

            var vcBoogieInfo = new VcBoogieInfo(vcinst, vcinstAxiom, vcAllAxioms, allAxiomsInfo);

            var vcProofData = new ProgramVcProofData(
                vcFunctions,
                vcBoogieInfo,
                vcHintManager,
                vcLocale,
                vcTranslator
            );

            var phasesTheories = new PhasesTheories(afterPassificationImpl.Name);

            var theoryPassive = VcPhaseManager.ProgramToVcProof(
                phasesTheories.TheoryName(PhasesTheories.Phase.Vc),
                _proofGenConfig.GenerateVcE2E,
                afterUnreachablePruningCfg,
                afterPassificationCfg,
                afterPassificationToAfterUnreachableBlock,
                afterPassificationToOrigBlock,
                passiveProgAccess,
                beforePassiveProgAccess,
                finalProgData,
                vcProofData,
                varTranslationFactory,
                typePremiseEraserFactory,
                gen,
                out var vcAssm,
                out var endToEndLemma
            );
            theories.Add(theoryPassive);

            #region before passive

            var passificationProgTheory = new Theory(beforePassiveProgTheoryName,
                new List<string> {"Boogie_Lang.Semantics", "Boogie_Lang.Util", beforeCfgToDagTheoryName},
                programDeclsBeforePassive);
            theories.Add(passificationProgTheory);

            /*
            Console.WriteLine("Passive prog mapping: " + fixedVarTranslation.OutputMapping());
            Console.WriteLine("Before passive prog mapping: " + fixedVarTranslation2.OutputMapping());
            */

            var passificationProofTheory = PassificationManager.PassificationProof(
                phasesTheories.TheoryName(PhasesTheories.Phase.Passification),
                theoryPassive.TheoryName,
                _proofGenConfig.GeneratePassifE2E,
                endToEndLemma,
                vcAssm,
                beforePassificationCfg,
                beforePassiveToAfterPassiveBlock,
                passiveRelationGen,
                beforePassiveProgAccess,
                passiveProgAccess,
                mainData,
                varTranslationFactory2,
                varTranslationFactory
            );
            theories.Add(passificationProofTheory);

            #endregion

            #region cfg to dag
            
            var uniqueExitBlock =
                uniqueExitBlockOrig != null
                    ? beforePassiveOrigBlock.First(kv => kv.Value == uniqueExitBlockOrig).Key
                    : null;


            var cfgToDagProofTheory = CfgToDagManager.CfgToDagProof(
                phasesTheories,
                _proofGenConfig.GenerateCfgDagE2E,
                vcAssm,
                beforeDagCfg,
                beforePassificationCfg,
                uniqueExitBlock,
                beforeDagData,
                cfgToDagHintManager,
                beforeDagAfterDagBlock,
                beforeCfgToDagProgAccess,
                beforePassiveProgAccess,
                varTranslationFactory2);
            theories.Add(cfgToDagProofTheory);
            #endregion
            
            StoreResult(afterPassificationImpl.Proc.Name, theories);
        }

        private static void StoreResult(string preferredDirName, IEnumerable<Theory> theories)
        {
            ProofGenerationOutput.StoreTheoriesInNewDirWithSession(preferredDirName, theories);
        }

        public static BoogieIsaProgInterface BoogieIsaProgInterface()
        {
            return new BoogieIsaProgInterface(new Dictionary<string, IProgramAccessor>(procNameToTopLevelPrograms), globalDataProgAccess);
        }
    }
}