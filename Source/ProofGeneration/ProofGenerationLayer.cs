using System;
using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;
using ProofGeneration.CFGRepresentation;
using ProofGeneration.Isa;
using ProofGeneration.VCProofGen;
using ProofGeneration.ProgramToVCProof;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Boogie.GraphUtil;
using Microsoft.Boogie.ProofGen;
using ProofGeneration.Util;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.BoogieIsaInterface.VariableTranslation;
using Microsoft.Boogie.TypeErasure;
using ProofGeneration.CfgToDag;
using ProofGeneration.Passification;

namespace ProofGeneration
{
    public class ProofGenerationLayer
    {
        private static Implementation afterPassificationImpl;

        private static IDictionary<Block, Block> beforeDagOrigBlock;
        private static IDictionary<Block, Block> beforeDagAfterDagBlock;
        private static CFGRepr beforeDagCfg;

        private static BoogieMethodData beforeDagData;
        
        private static IDictionary<Block, Block> beforePassiveOrigBlock;
        private static CFGRepr beforePassificationCfg;

        private static BoogieMethodData beforePassiveData;

        private static CFGRepr afterPassificationCfg;
        private static CFGRepr noEmptyBlocksCfg;
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

        public static void Program(Program p)
        {
            boogieGlobalData = new BoogieGlobalData(p.Functions, p.Axioms, p.GlobalVariables, p.Constants);
        }

        public static void BeforeCFGToDAG(Implementation impl)
        {
            beforeDagCfg = CFGReprTransformer.GetCfgRepresentation(impl, 
                true, 
                true, 
                out beforeDagOrigBlock, 
                out List<Variable> newVarsFromDesugaring, 
                false);
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
            beforePassificationCfg = CFGReprTransformer.GetCfgRepresentation(
                impl, 
                true,
                true,
                out beforePassiveOrigBlock,
                out List<Variable> newVarsFromDesugaring
                );
            cfgToDagHintManager.AfterDagToOrig = beforePassiveOrigBlock;
            beforePassiveData = MethodDataFromImpl(impl, boogieGlobalData, newVarsFromDesugaring);
            passificationHintManager = new PassificationHintManager(beforePassiveOrigBlock);
            initialVarMapping = new Dictionary<Block, IDictionary<Variable, Expr>>();
            
            // compute mapping between copied blocks (before dag -> after dag)
            beforeDagAfterDagBlock = new Dictionary<Block, Block>();
            var origToAfterDag = beforePassiveOrigBlock.ToDictionary(x => x.Value, x => x.Key);

            foreach (var beforeBlock in beforeDagCfg.GetBlocksForwards())
            {
                var origBlock = beforeDagOrigBlock[beforeBlock];
                beforeDagAfterDagBlock.Add(beforeBlock, origToAfterDag[origBlock]);
            }
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
            Substitution formalProcImplSubst = Substituter.SubstitutionFromHashtable(impl.GetImplFormalMap());
            List<Expr> preconditions = new List<Expr>();
            foreach (Requires req in impl.Proc.Requires)
            {
                if (!req.Free)
                {
                    // skip free ensures clauses
                    Expr e = Substituter.Apply(formalProcImplSubst, req.Condition);
                    preconditions.Add(e);
                }
                else
                {
                    throw new ProofGenUnexpectedStateException("Don't support free precondition");
                }
            }
            List<Expr> postconditions = new List<Expr>();
            foreach (Ensures ens in impl.Proc.Ensures)
            {
                if (!ens.Free)
                {
                    // skip free ensures clauses
                    Expr e = Substituter.Apply(formalProcImplSubst, ens.Condition);
                    postconditions.Add(e);
                }
                else
                {
                    throw new ProofGenUnexpectedStateException("Don't support free postcondition");
                }
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

        public static void AfterPassificationCheckGlobalMap(Implementation impl)
        {
            finalProgData = MethodDataFromImpl(impl, boogieGlobalData);
            afterPassificationImpl = impl;
            afterPassificationCfg = CFGReprTransformer.getCFGRepresentation(impl);

            var passiveBlocks = new List<Block>(impl.Blocks);
            
            GlobalVersion globalVersion = new GlobalVersion();

            passiveRelationGen = new PassiveRelationGen(
                beforePassificationCfg,
                passificationHintManager,
                initialVarMapping,
                beforePassiveOrigBlock,
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
                GlobalVersionChecker.CheckVersionMap(globalVersionMap, passiveRelationGen, beforePassificationCfg, beforePassiveOrigBlock);

            if (!versionMapCorrect)
            {
                throw new ProofGenUnexpectedStateException(typeof(ProofGenerationLayer), "Incorrect version map");
            }
        }

        /*
        public static void AfterEmptyBlockRemoval(Implementation impl)
        {
            need to check predecessor issue
            //beforeDagCfg = CFGReprTransformer.GetCfgRepresentation(impl, true, out beforeDagOrigBlock, false);
            // noEmptyBlocksCfg = CFGReprTransformer.getCFGRepresentation(impl);
        }
        */

        public static void AfterUnreachablePruning(Implementation impl)
        {
            afterUnreachablePruningCfg = CFGReprTransformer.getCFGRepresentation(impl);
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
            IsaUniqueNamer uniqueNamer = new IsaUniqueNamer();
            /* Hack: try to make sure unique namer uses names for Boogie functions and Boogie variables that are different
             * from the default name otherwise it clashes with the functions potentially fixed in the context of a locale
             */
            foreach(var fun in boogieGlobalData.Functions)
            {
                uniqueNamer.GetName(fun.Name, "o123_"+fun.Name);
            }
            
            foreach(var variable in finalProgData.AllVariables())
            {
                uniqueNamer.GetName(variable.Name, "o123_" + variable.Name);
            }

            //Hack: translate vc variable based on name, to ensure that applying erasure multiple times shares the same variables
            var translator = VCExprToIsaTranslator.CreateNameBasedTranslator(uniqueNamer);
            translator.SetFunctionNamer(uniqueNamer);
            translator.SetTryInstantiatingFunctions(true);
            vcHintManager = new VCHintManager(new VcRewriteLemmaGen(factory, translator));
        }
        
        private static ProofGenConfig _proofGenConfig = 
            new ProofGenConfig(false, false, true);

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
            if(axiomBuilder == null && typeAxioms != null)
                throw new ArgumentException("type axioms can only be null if axiom builder is null");
            
            var fixedVarTranslation2 = new DeBruijnFixedVarTranslation(beforePassiveData);
            var fixedTyVarTranslation2 = new DeBruijnFixedTVarTranslation(beforePassiveData);
            var varTranslationFactory2 = new DeBruijnVarFactory(fixedVarTranslation2, fixedTyVarTranslation2, boogieGlobalData);
            
            #region before cfg to dag program
            string beforeCfgToDagTheoryName = afterPassificationImpl.Name + "_before_cfg_to_dag_prog";
            var beforeCfgToDagConfig = new IsaProgramGeneratorConfig(null, true,true, true, true);
            var beforeCfgToDagProgAccess = new IsaProgramGenerator().GetIsaProgram(
                beforeCfgToDagTheoryName, 
                afterPassificationImpl.Name, 
                beforePassiveData, beforeCfgToDagConfig, varTranslationFactory2, 
                beforeDagCfg, 
                out IList<OuterDecl> programDeclsBeforeCfgToDag);
            #endregion
            
            #region before passive program

            //Console.WriteLine("**Before passive prog mapping: " + fixedVarTranslation2.OutputMapping());
            
            string beforePassiveProgTheoryName = afterPassificationImpl.Name + "_before_passive_prog";
            var beforePassiveConfig = new IsaProgramGeneratorConfig(beforeCfgToDagProgAccess, false,false, false, false);
            var beforePassiveProgAccess = new IsaProgramGenerator().GetIsaProgram(beforePassiveProgTheoryName, 
                afterPassificationImpl.Name, 
                beforePassiveData, beforePassiveConfig, varTranslationFactory2, 
                beforePassificationCfg, 
                out IList<OuterDecl> programDeclsBeforePassive);
            #endregion


            IEnumerable<VCExpr> vcAllAxioms = AxiomHandler.AxiomInfo(
                axiomBuilder != null,
                boogieGlobalData.Axioms,
                vcAxioms,
                typeAxioms,
                typeAxiomInfo, 
                out List<VCAxiomInfo> allAxiomsInfo);
            
            LocaleDecl vcLocale = VCToIsaInterface.ConvertVC(
                "vc",
                vc,
                vcAllAxioms,
                new StandardActiveDecl(),
                translator,
                axiomBuilder,
                finalProgData,
                afterUnreachablePruningCfg,
                out VCInstantiation<Block> vcinst,
                out VCInstantiation<VCExpr> vcinstAxiom,
                out IVCVarFunTranslator vcTranslator,
                out IEnumerable<Function> vcFunctions);
            
            //use global version map for translation 
            var fixedVarTranslation = new SimpleFixedVarTranslation(globalVersionMap);
            var fixedTyVarTranslation = new DeBruijnFixedTVarTranslation(finalProgData);
            varTranslationFactory = new DeBruijnVarFactory(fixedVarTranslation, fixedTyVarTranslation, boogieGlobalData);

            string finalProgTheoryName = afterPassificationImpl.Name + "_passive_prog";
            var passiveProgConfig = new IsaProgramGeneratorConfig(beforePassiveProgAccess, false, false, false, false);
            var passiveProgAccess = new IsaProgramGenerator().GetIsaProgram(finalProgTheoryName, 
                afterPassificationImpl.Name, 
                finalProgData, passiveProgConfig, varTranslationFactory, 
                //we use the CFG before the peep-hole transformations, so that we can directly use the VC to program proof in the passification phase
                afterPassificationCfg,  
                out IList<OuterDecl> programDecls);
            
            Theory finalProgTheory =
                new Theory(finalProgTheoryName, new List<string> { "Boogie_Lang.Semantics", "Boogie_Lang.Util", beforePassiveProgAccess.TheoryName() }, programDecls);
            theories.Add(finalProgTheory);
                
            var vcBoogieInfo = new VcBoogieInfo(vcinst, vcinstAxiom, vcAllAxioms, allAxiomsInfo);
            
            var vcProofData = new ProgramVcProofData(
                vcFunctions,
                vcBoogieInfo,
                vcHintManager,
                vcLocale,
                vcTranslator
                );
            Theory theoryPassive = VcPhaseManager.ProgramToVcProof(
                afterPassificationImpl.Name + "_vcphase_proof",
                _proofGenConfig.GenerateVcE2E,
                afterUnreachablePruningCfg,
                afterPassificationCfg,
                passiveProgAccess,
                beforePassiveProgAccess,
                finalProgData,
                vcProofData,
                varTranslationFactory,
                typePremiseEraserFactory,
                gen,
                out Term vcAssm,
                out LemmaDecl endToEndLemma
            );
            theories.Add(theoryPassive);
            
            #region before passive
            
            Theory passificationProgTheory = new Theory(beforePassiveProgTheoryName,
                new List<string> {"Boogie_Lang.Semantics", "Boogie_Lang.Util", beforeCfgToDagTheoryName}, programDeclsBeforePassive);
            theories.Add(passificationProgTheory);
            
            Console.WriteLine("Passive prog mapping: " + fixedVarTranslation.OutputMapping());
            Console.WriteLine("Before passive prog mapping: " + fixedVarTranslation2.OutputMapping());

            
            Theory passificationProofTheory = PassificationManager.PassificationProof(
                afterPassificationImpl.Name+"_passification_proof",
                theoryPassive.theoryName,
                _proofGenConfig.GeneratePassifE2E,
                endToEndLemma,
                vcAssm,
                beforePassificationCfg,
                beforePassiveOrigBlock,
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
            Theory beforeCfgToDagProgTheory = new Theory(beforeCfgToDagTheoryName,
                new List<string> {"Boogie_Lang.Semantics", "Boogie_Lang.TypeSafety", "Boogie_Lang.Util"}, programDeclsBeforeCfgToDag);
            theories.Add(beforeCfgToDagProgTheory);

            Block uniqueExitBlock =
                uniqueExitBlockOrig != null
                    ? beforePassiveOrigBlock.First(kv => kv.Value == uniqueExitBlockOrig).Key
                    : null;
                

            Theory cfgToDagProofTheory = CfgToDagManager.CfgToDagProof(
                afterPassificationImpl.Name+"_cfg_to_dag_proof",
                beforeDagCfg,
                beforePassificationCfg,
                uniqueExitBlock,
                beforeDagData,
                cfgToDagHintManager,
                beforeDagAfterDagBlock,
                beforeCfgToDagProgAccess,
                beforePassiveProgAccess,
                varTranslationFactory2);
            //theories.Add(cfgToDagProofTheory);
            #endregion
            
            ProofGenerationOutput.StoreProofs("proofs_"+afterPassificationImpl.Proc.Name, theories);
            
        }

    }

}
