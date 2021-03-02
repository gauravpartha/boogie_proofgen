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

        public static void Program(Program p)
        {
            boogieGlobalData = new BoogieGlobalData(p.Functions, p.Axioms, p.GlobalVariables, p.Constants);
        }

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

        /// <param name="g">graph for which all the loop information has been computed</param>
        public static void GraphCfgToDag(Graph<Block> g)
        {
            cfgToDagHintManager = new CfgToDagHintManager(g, beforeDagOrigBlock);
        }

        public static void CreateUnifiedExitBlock(Block generatedExitBlock)
        {
            uniqueExitBlockOrig = generatedExitBlock;
        }

        public static void BeforePassification(Implementation impl)
        {
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
            var preconditions = new List<Expr>();
            foreach (var req in impl.Proc.Requires)
                if (!req.Free)
                {
                    // skip free ensures clauses
                    var e = Substituter.Apply(formalProcImplSubst, req.Condition);
                    preconditions.Add(e);
                }
                else
                {
                    throw new ProofGenUnexpectedStateException("Don't support free precondition");
                }

            var postconditions = new List<Expr>();
            foreach (var ens in impl.Proc.Ensures)
                if (!ens.Free)
                {
                    // skip free ensures clauses
                    var e = Substituter.Apply(formalProcImplSubst, ens.Condition);
                    postconditions.Add(e);
                }
                else
                {
                    throw new ProofGenUnexpectedStateException("Don't support free postcondition");
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

        public static void RecordInitialVariableMapping(Block b, IDictionary<Variable, Expr> variableToExpr)
        {
            Contract.Requires(b != null);
            Contract.Requires(variableToExpr != null);

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

        public static void AfterPassificationCheckGlobalMap(Implementation impl)
        {
            finalProgData = MethodDataFromImpl(impl, boogieGlobalData);
            afterPassificationImpl = impl;
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

        public static void AfterUnreachablePruning(Implementation impl)
        {
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
            vcHintManager.NextHintForBlock(cmd, block, exprVC, postVC, resultVC, subsumptionOption);
        }

        public static void NextPassificationHint(Block block, Cmd cmd, Variable origVar, Expr passiveExpr)
        {
            passificationHintManager.AddHint(block, cmd, origVar, passiveExpr);
        }

        public static void LoopHeadHint(Block block, IEnumerable<Variable> varsToHavoc, IEnumerable<Expr> invariants)
        {
            cfgToDagHintManager.AddHint(block, new LoopHeadHint(varsToHavoc, invariants));
        }

        public static void NewBackedgeBlock(Block oldBackedgeBlock, Block newBackedgeBlock, Block loopHead)
        {
            cfgToDagHintManager.AddNewBackedgeBlock(newBackedgeBlock, loopHead);
        }

        public static void SetTypeEraserFactory(TypePremiseEraserFactory factory)
        {
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

        //axiom builder is null iff types are not erased (since no polymorphism in vc)
        public static void VCGenerateAllProofs(
            VCExpr vc,
            VCExpr vcAxioms,
            VCExpr typeAxioms,
            List<VCAxiomInfo> typeAxiomInfo,
            VCExpressionGenerator gen,
            Boogie2VCExprTranslator translator,
            TypeAxiomBuilderPremisses axiomBuilder)
        {
            var theories = new List<Theory>();
            if (axiomBuilder == null && typeAxioms != null)
                throw new ArgumentException("type axioms can only be null if axiom builder is null");

            var fixedVarTranslation2 = new DeBruijnFixedVarTranslation(beforePassiveData);
            var fixedTyVarTranslation2 = new DeBruijnFixedTVarTranslation(beforePassiveData);
            var varTranslationFactory2 =
                new DeBruijnVarFactory(fixedVarTranslation2, fixedTyVarTranslation2, boogieGlobalData);

            #region before cfg to dag program

            var beforeCfgToDagTheoryName = afterPassificationImpl.Name + "_before_cfg_to_dag_prog";
            var beforeCfgToDagConfig = new IsaProgramGeneratorConfig(null, true, true, true, true, true);
            var beforeCfgToDagProgAccess = new IsaProgramGenerator().GetIsaProgram(
                beforeCfgToDagTheoryName,
                afterPassificationImpl.Name,
                beforePassiveData, beforeCfgToDagConfig, varTranslationFactory2,
                beforeDagCfg,
                out var programDeclsBeforeCfgToDag);

            #endregion

            #region before passive program

            var beforePassiveProgTheoryName = afterPassificationImpl.Name + "_before_passive_prog";
            var beforePassiveConfig =
                new IsaProgramGeneratorConfig(beforeCfgToDagProgAccess, false, false, false, false, false);
            var beforePassiveProgAccess = new IsaProgramGenerator().GetIsaProgram(beforePassiveProgTheoryName,
                afterPassificationImpl.Name,
                beforePassiveData, beforePassiveConfig, varTranslationFactory2,
                beforePassificationCfg,
                out var programDeclsBeforePassive);

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

            var finalProgTheoryName = afterPassificationImpl.Name + "_passive_prog";
            var passiveProgConfig =
                new IsaProgramGeneratorConfig(beforePassiveProgAccess, false, false, false, true, false);
            var passiveProgAccess = new IsaProgramGenerator().GetIsaProgram(finalProgTheoryName,
                afterPassificationImpl.Name,
                finalProgData, passiveProgConfig, varTranslationFactory,
                //we use the CFG before the peep-hole transformations, so that we can directly use the VC to program proof in the passification phase
                afterPassificationCfg,
                out var programDecls);

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

            Console.WriteLine("Passive prog mapping: " + fixedVarTranslation.OutputMapping());
            Console.WriteLine("Before passive prog mapping: " + fixedVarTranslation2.OutputMapping());


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
                beforePassiveData,
                varTranslationFactory2,
                varTranslationFactory
            );
            theories.Add(passificationProofTheory);

            #endregion

            #region cfg to dag

            var beforeCfgToDagProgTheory = new Theory(beforeCfgToDagTheoryName,
                new List<string> {"Boogie_Lang.Semantics", "Boogie_Lang.TypeSafety", "Boogie_Lang.Util"},
                programDeclsBeforeCfgToDag);
            theories.Add(beforeCfgToDagProgTheory);

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

            ProofGenerationOutput.StoreProofs("proofs_" + afterPassificationImpl.Proc.Name, theories);
        }
    }
}