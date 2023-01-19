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
using ProofGeneration.ASTRepresentation;
using ProofGeneration.AstToCfg;
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
        private static Implementation beforeCFGtoDagImpl;

        //private static Implementation beforeDagImpl;
        private static AstToCfgProofGenInfo proofGenInfo;
        
        private static MultiCmdIsaVisitor cmdIsaVisitor;

        private static ASTRepr beforeCfgAst;
        private static IDictionary<BigBlock, Block> beforeCfgAfterCfgBlock;
        //private static BoogieMethodData beforeCfgData;

        private static IDictionary<Block, Block> beforeOptimizationsOrigBlock;
        private static IDictionary<Block, Block> beforeDagOrigBlock;
        private static IDictionary<Block, Block> beforeDagAfterDagBlock;
        
        private static CFGRepr beforeOptimizationsCFG;

        private static CFGRepr beforeDagCfg;

        private static BoogieMethodData beforeOptimizationsData;
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

        //private static Block uniqueExitBlockOrigBeforeOptimizations;
        private static Block uniqueExitBlockOrig;

        private static ProofGenConfig _proofGenConfig = 
          new(true, false, false, false, false,
              false, false, false, false, 
              false, false, false, false);

        private static IProgramAccessor globalDataProgAccess;

        private static IsaUniqueNamer uniqueNamer;

        private static IDictionary<string, IProgramAccessor> procNameToTopLevelPrograms = new Dictionary<string, IProgramAccessor>();
        
        /// <summary>
        /// Provide program for the next procedure (for the global declarations).
        /// </summary>
        public static void Program(Program p)
        {
            if (uniqueNamer == null)
            {
              uniqueNamer = new IsaUniqueNamer();
            }

            if (boogieGlobalData == null)
            {
                boogieGlobalData = new BoogieGlobalData(p.Functions, p.Axioms, p.GlobalVariables, p.Constants);

                var methodData = BoogieMethodData.CreateOnlyGlobal(boogieGlobalData);
                var fixedVarTranslation = new DeBruijnFixedVarTranslation(methodData);
                var fixedTyVarTranslation = new DeBruijnFixedTVarTranslation(methodData);
                var factory =
                    new DeBruijnVarFactory(fixedVarTranslation, fixedTyVarTranslation, boogieGlobalData);
                var globalDataTheoryName = "global_data";
                var globalDataConfig = new IsaProgramGeneratorConfig(null, 
                  true, 
                  true, 
                  true, 
                  false, 
                  SpecsConfig.None, 
                  false);
                globalDataProgAccess = new IsaProgramGenerator().GetIsaProgram(
                    globalDataTheoryName,
                    "proc",
                    methodData, globalDataConfig, factory, 
                    null,
                    uniqueNamer,
                    out var declsGlobalData,
                    CommandLineOptions.Clo.GenerateMembershipLemmas(),
                    true
                );
                
                var globalDataTheory = new Theory(globalDataTheoryName,
                    new List<string> {"Boogie_Lang.Semantics", "Boogie_Lang.TypeSafety", "Boogie_Lang.Util"},
                    declsGlobalData);
                ProofGenerationOutput.StoreTheoriesTopLevel(new List<Theory> { globalDataTheory });
            }
        }

        private static bool AstContainsGotoOrBreak(AstToCfgProofGenInfo proofGenInfo)
        {
          IList<BigBlock> ast = proofGenInfo.GetBigBlocks();
          foreach (var b in ast)
          {
            if (b.ec is BreakCmd || b.tc is GotoCmd)
            {
              return true;
            }
          }

          return false;
        }
        
        private static bool checkForGotos(StmtList stmtList)
        {
          foreach (var bb in stmtList.BigBlocks)
          {
            if (bb.tc is GotoCmd)
            {
              return true;
            }

            if (bb.ec is IfCmd ifcmd)
            {
              checkForGotos(ifcmd.thn);
              checkForGotos(ifcmd.elseBlock);
            }
            else if (bb.ec is WhileCmd whilecmd)
            {
              checkForGotos(whilecmd.Body);
            }
          }

          return false;
        }
        
        public static void BeforeOptimizations(Implementation impl)
        {
          var config = new CFGReprConfigBuilder().SetIsAcyclic(false).SetBlockCopy(true).SetDesugarCalls(true)
            .Build();
          beforeOptimizationsCFG = CFGReprTransformer.GetCfgRepresentation(impl,
            config,
            out beforeOptimizationsOrigBlock,
            out var newVarsFromDesugaring);
          beforeOptimizationsData = MethodDataFromImpl(impl, boogieGlobalData, newVarsFromDesugaring);
        }

        /// <summary>
        /// Provide source CFG for CFG-to-DAG phase
        /// </summary>
        public static void BeforeCFGToDAG(Implementation impl)
        {
            beforeCFGtoDagImpl = impl;  
          
            var config = new CFGReprConfigBuilder().SetIsAcyclic(false).SetBlockCopy(true).SetDesugarCalls(true)
                .Build();
            beforeDagCfg = CFGReprTransformer.GetCfgRepresentation(impl,
                config,
                out beforeDagOrigBlock,
                out var newVarsFromDesugaring);

            foreach (var block in impl.Blocks)
            {
              if (beforeDagOrigBlock.Values.Contains(block))
              {
                continue;
              }
              else
              {
                throw new Exception();
              }
            }
            
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
            if (CommandLineOptions.Clo.OnlyGenerateInitialProgramIsa())
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
            if (CommandLineOptions.Clo.OnlyGenerateInitialProgramIsa())
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
            if (CommandLineOptions.Clo.OnlyGenerateInitialProgramIsa())
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
            if (CommandLineOptions.Clo.OnlyGenerateInitialProgramIsa())
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
            if (CommandLineOptions.Clo.OnlyGenerateInitialProgramIsa())
                return;
            vcHintManager.NextHintForBlock(cmd, block, exprVC, postVC, resultVC, subsumptionOption);
        }
        

        /// <summary>
        /// Boogie transforms VC used for current procedure to "true", since there are no assertions. 
        /// </summary>
        public static void VcIsTrivial()
        {
          vcHintManager.TransformHintsToTrivialVc();
        }

        /// <summary>
        /// Provide a hint that passification of the non-passive command <paramref name="cmd"/> in block
        /// <paramref name="block"/> leads to non-passive variable <paramref name="origVar"/> being related to
        /// passive expression <paramref name="passiveExpr"/>
        /// </summary>
        public static void NextPassificationHint(Block block, Cmd cmd, Variable origVar, Expr passiveExpr)
        {
            if (CommandLineOptions.Clo.OnlyGenerateInitialProgramIsa())
                return;
            passificationHintManager.AddHint(block, cmd, origVar, passiveExpr);
        }

        /// <summary>
        /// Provide hint that <paramref name="block"/> is a loop head of a loop with invariants <paramref name="invariants"/>
        /// and modified variables <paramref name="varsToHavoc"/>
        /// </summary>
        public static void LoopHeadHint(Block block, IEnumerable<Variable> varsToHavoc, IEnumerable<Expr> invariants)
        {
            if (CommandLineOptions.Clo.OnlyGenerateInitialProgramIsa())
                return;
            cfgToDagHintManager.AddHint(block, new LoopHeadHint(varsToHavoc, invariants));
        }

        /// <summary>
        /// Provide hint that the backedge block <paramref name="oldBackedgeBlock"/> is replaced by a new backedge block
        /// <paramref name="newBackedgeBlock"/> for a loop with loop head <paramref name="loopHead"/>.
        /// </summary>
        public static void NewBackedgeBlock(Block oldBackedgeBlock, Block newBackedgeBlock, Block loopHead)
        {
            if (CommandLineOptions.Clo.OnlyGenerateInitialProgramIsa())
                return;
            cfgToDagHintManager.AddNewBackedgeBlock(newBackedgeBlock, loopHead);
        }

        public static void SetTypeEraserFactory(TypePremiseEraserFactory factory)
        {
            if (CommandLineOptions.Clo.OnlyGenerateInitialProgramIsa())
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

        private static void DesugarCmdsInBigBlock(BigBlock b)
        {
          List<Cmd> copyCmds = new List<Cmd>();
          List<Variable> newVarsFromDesugaring = new List<Variable>();
          foreach (Cmd cmd in b.simpleCmds)
          {

            if (cmd is SugaredCmd sugaredCmd)
            {
              var stateCmd = sugaredCmd.Desugaring as StateCmd;
              if (stateCmd != null)
              {
                newVarsFromDesugaring.AddRange(stateCmd.Locals);
                foreach (var desugaredCmd in stateCmd.Cmds)
                {
                  copyCmds.Add(desugaredCmd);
                }
              }
            }
            else
            {
              copyCmds.Add(cmd);
            }
          }

          proofGenInfo.GetNewVarsFromDesugaring().AddRange(newVarsFromDesugaring);
          b.simpleCmds = copyCmds;

          if (b.ec is IfCmd ifCmd)
          {
            foreach (var then_bb in ifCmd.thn.BigBlocks)
            {
              DesugarCmdsInBigBlock(then_bb);
            }

            foreach (var else_bb in ifCmd.elseBlock.BigBlocks)
            {
              DesugarCmdsInBigBlock(else_bb);
            }
          }
          else if (b.ec is WhileCmd wcmd)
          {
            foreach (var body_bb in wcmd.Body.BigBlocks)
            {
              DesugarCmdsInBigBlock(body_bb);
            }
          }
        }

        public static bool GenerateAstCfgE2E()
        {
          return _proofGenConfig.GenerateAstCfgE2E;
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
            var map = AstToCfgProofGenInfoManager.GetImplToProofGenInfo();
            proofGenInfo = map[afterPassificationImpl];

            if (AstContainsGotoOrBreak(proofGenInfo))
            {
              _proofGenConfig.GenerateAstCfgProof = false;
            }

            IList<BigBlock> bigBlocks = proofGenInfo.GetBigBlocks();
            foreach (BigBlock b in bigBlocks)
            {
              DesugarCmdsInBigBlock(b);
            }
            
            _proofGenConfig.GeneratePassifE2E = _proofGenConfig.GenerateVcProof && _proofGenConfig.GenerateVcE2E && _proofGenConfig.GeneratePassifProof;
            _proofGenConfig.GenerateCfgDagE2E = _proofGenConfig.GeneratePassifProof && _proofGenConfig.GeneratePassifE2E && _proofGenConfig.GenerateCfgDagProof;
            _proofGenConfig.GenerateAstCfgE2E = _proofGenConfig.GenerateCfgDagProof && _proofGenConfig.GenerateCfgDagE2E && _proofGenConfig.GenerateAstCfgProof;

            _proofGenConfig.GenerateBeforeAstCfgProg = _proofGenConfig.GenerateAstCfgProof;
            _proofGenConfig.GenerateUnoptimizedCfgProg = proofGenInfo.GetOptimizationsFlag() && _proofGenConfig.GenerateAstCfgProof;
            _proofGenConfig.GenerateBeforeCfgDagProg = (proofGenInfo.GetOptimizationsFlag() &&  _proofGenConfig.GenerateCfgDagProof) || 
                                                       (!proofGenInfo.GetOptimizationsFlag() && (_proofGenConfig.GenerateAstCfgProof || _proofGenConfig.GenerateCfgDagProof));
            _proofGenConfig.GenerateBeforePassifProg = _proofGenConfig.GenerateCfgDagProof || _proofGenConfig.GeneratePassifProof;
            _proofGenConfig.GeneratePassifiedProg = _proofGenConfig.GeneratePassifProof || _proofGenConfig.GenerateVcProof;

            IList<Block> unoptimizedCFGBlocks = proofGenInfo.GetUnpotimizedBlocks(); 
            var newToOldInternal = new Dictionary<Block, Block>();
            unoptimizedCFGBlocks.ZipDo(afterPassificationImpl.Blocks, (bNew, bOld) => newToOldInternal.Add(bNew, bOld));
            beforeOptimizationsOrigBlock = newToOldInternal;
            
            beforeOptimizationsData = MethodDataFromImpl(afterPassificationImpl, boogieGlobalData, proofGenInfo.GetNewVarsCFG());
            var config = new CFGReprConfigBuilder().SetIsAcyclic(false).SetBlockCopy(true).SetDesugarCalls(true)
              .Build();
            
            IDictionary<Block, int> labeling;
            if (config.IsAcyclic)
            {
              labeling = CFGReprTransformer.GetTopologicalLabeling(unoptimizedCFGBlocks);
            }
            else
            {
              labeling = new Dictionary<Block, int>();
              var idx = 0;
              foreach (var b in unoptimizedCFGBlocks)
              {
                labeling.Add(b, idx);
                idx++;
              }
            }
            
            IDictionary<Block, IList<Block>> outgoingBlocks = new Dictionary<Block, IList<Block>>();
            foreach (var block in unoptimizedCFGBlocks)
            {
              var curOutgoing = new List<Block>();
              if (block.TransferCmd is GotoCmd gotoCmd) curOutgoing.AddRange(gotoCmd.labelTargets);
              outgoingBlocks.Add(block, curOutgoing);
            }

            Block entryBlock = null;
            foreach (var block in unoptimizedCFGBlocks)
            {
              if (block.Predecessors.Count == 0)
              {
                if (entryBlock != null)
                  throw new ProofGenUnexpectedStateException(typeof(CFGReprTransformer), "no unique CFG entry");
                entryBlock = block;
              }
            }
            
            beforeOptimizationsCFG = new CFGRepr(outgoingBlocks, labeling, entryBlock);

            if (uniqueNamer == null)
            {
              uniqueNamer = new IsaUniqueNamer();
            }

            var theories = new List<Theory>();
            if (axiomBuilder == null && typeAxioms != null)
                throw new ArgumentException("type axioms can only be null if axiom builder is null");

            /* Since in the proofs calls are desugared, there can be more variables in "beforePassiveData". If only
             the program should be generated, then these variables should be ignored. */
            var mainData = CommandLineOptions.Clo.OnlyGenerateInitialProgramIsa() ? beforeDagData : beforePassiveData;
            
            var fixedVarTranslation2 = new DeBruijnFixedVarTranslation(mainData);
            var fixedTyVarTranslation2 = new DeBruijnFixedTVarTranslation(mainData);
            var varTranslationFactory2 =
                new DeBruijnVarFactory(fixedVarTranslation2, fixedTyVarTranslation2, boogieGlobalData);
            
            cmdIsaVisitor = new MultiCmdIsaVisitor(varTranslationFactory2);

            IProgramAccessor beforeAstToCfgProgAccess = null;
            IProgramAccessor unoptimizedCfgProgAccess = null;
            IProgramAccessor beforeCfgToDagProgAccess = null;
            IProgramAccessor beforePassiveProgAccess = null;
            IProgramAccessor passiveProgAccess = null;

            if (_proofGenConfig.GenerateBeforeAstCfgProg || CommandLineOptions.Clo.OnlyGenerateInitialProgramIsa())
            {
              #region before ast to cfg program

              beforeCfgAst = new ASTRepr(proofGenInfo.GetBigBlocks());
              ASTRepr originalAst = new ASTRepr(proofGenInfo.GetOriginalAst());

              var beforeAstToCfgTheoryName =
                uniqueNamer.GetName(afterPassificationImpl.Name + "_before_ast_to_cfg_prog");
              //Hack: specs config used to distinguish between all (free + checks) (--> expression tuples) or just checked (no tuples)
              var specsConfig_ast = CommandLineOptions.Clo.OnlyGenerateInitialProgramIsa()
                ? SpecsConfig.All
                : SpecsConfig.AllPreCheckedPost;
              var beforeAstToCfgConfig = new IsaProgramGeneratorConfig(globalDataProgAccess,
                false,
                false,
                false,
                true,
                specsConfig_ast,
                true);

              beforeAstToCfgProgAccess = new IsaProgramGeneratorForAst().GetIsaProgram(
                beforeAstToCfgTheoryName,
                afterPassificationImpl.Name,
                mainData, beforeAstToCfgConfig, varTranslationFactory2,
                beforeCfgAst,
                originalAst,
                proofGenInfo,
                uniqueNamer,
                out var programDeclsBeforeAstToCfg,
                CommandLineOptions.Clo.GenerateMembershipLemmas());
              procNameToTopLevelPrograms.Add(afterPassificationImpl.Proc.Name + "ast", beforeAstToCfgProgAccess);

              var beforeAstToCfgProgTheory = new Theory(beforeAstToCfgTheoryName,
                new List<string>
                {
                  "Boogie_Lang.Ast", "Boogie_Lang.Semantics", "Boogie_Lang.TypeSafety", "Boogie_Lang.Util",
                  "\"../" + globalDataProgAccess.TheoryName() + "\""
                },
                programDeclsBeforeAstToCfg);
              theories.Add(beforeAstToCfgProgTheory);
              
              if(CommandLineOptions.Clo.OnlyGenerateInitialProgramIsa())
              {
                StoreResult(uniqueNamer.GetName(afterPassificationImpl.Proc.Name), theories);
                return;
              }

              #endregion
            }

            if (_proofGenConfig.GenerateUnoptimizedCfgProg)
            {
                #region unoptimized cfg program

                var unoptimizedCfgTheoryName =
                  uniqueNamer.GetName(afterPassificationImpl.Name + "_unoptimized_cfg_prog");
                //Hack: specs config used to distinguish between all (free + checks) (--> expression tuples) or just checked (no tuples)
                var _specsConfig = CommandLineOptions.Clo.OnlyGenerateInitialProgramIsa()
                  ? SpecsConfig.All
                  : SpecsConfig.AllPreCheckedPost;
                var unoptimizedCfgConfig =
                  new IsaProgramGeneratorConfig(beforeAstToCfgProgAccess, 
                    false, 
                    false, 
                    false, 
                    false, 
                    _specsConfig, 
                    false);
                
                unoptimizedCfgProgAccess = new IsaProgramGenerator().GetIsaProgram(
                  unoptimizedCfgTheoryName,
                  afterPassificationImpl.Name,
                  mainData, unoptimizedCfgConfig, varTranslationFactory2,
                  beforeOptimizationsCFG,
                  uniqueNamer,
                  out var programDeclsUnoptimizedCfg,
                  CommandLineOptions.Clo.GenerateMembershipLemmas());
                procNameToTopLevelPrograms.Add(afterPassificationImpl.Proc.Name + "unoptimized",
                  unoptimizedCfgProgAccess);

                var unoptimizedCfgProgTheory = new Theory(unoptimizedCfgTheoryName,
                  new List<string>
                  {
                    "Boogie_Lang.Semantics", "Boogie_Lang.TypeSafety", "Boogie_Lang.Util",
                    beforeAstToCfgProgAccess.TheoryName()
                  },
                  programDeclsUnoptimizedCfg);
                theories.Add(unoptimizedCfgProgTheory);

                #endregion
            }

            if (_proofGenConfig.GenerateBeforeCfgDagProg)
            {
              #region before cfg to dag program
              var beforeCfgToDagTheoryName = uniqueNamer.GetName(afterPassificationImpl.Name + "_before_cfg_to_dag_prog");
              //Hack: specs config used to distinguish between all (free + checks) (--> expression tuples) or just checked (no tuples)
              var specsConfig = CommandLineOptions.Clo.OnlyGenerateInitialProgramIsa() ? SpecsConfig.All : SpecsConfig.AllPreCheckedPost;
              var beforeCfgToDagConfig = new IsaProgramGeneratorConfig(globalDataProgAccess, 
                false, 
                false, 
                false, 
                true, 
                specsConfig, 
                true);
              beforeCfgToDagProgAccess = new IsaProgramGenerator().GetIsaProgram(
                beforeCfgToDagTheoryName,
                afterPassificationImpl.Name,
                mainData, beforeCfgToDagConfig, varTranslationFactory2,
                beforeDagCfg,
                uniqueNamer,
                out var programDeclsBeforeCfgToDag,
                CommandLineOptions.Clo.GenerateMembershipLemmas());
              procNameToTopLevelPrograms.Add(afterPassificationImpl.Proc.Name, beforeCfgToDagProgAccess);
            
              var beforeCfgToDagProgTheory = new Theory(beforeCfgToDagTheoryName,
                new List<string> {"Boogie_Lang.Semantics", "Boogie_Lang.TypeSafety", "Boogie_Lang.Util", "\"../"+globalDataProgAccess.TheoryName()+"\""},
                programDeclsBeforeCfgToDag);
              theories.Add(beforeCfgToDagProgTheory);
              #endregion
            }
            
            var theoryNameForParentImport = _proofGenConfig.GenerateAstCfgProof
              ? beforeAstToCfgProgAccess.TheoryName()
              : _proofGenConfig.GenerateBeforeCfgDagProg ? beforeCfgToDagProgAccess.TheoryName() : "";

            if (_proofGenConfig.GenerateBeforePassifProg)
            {
              #region before passive program

              IProgramAccessor parentProgramAccessorForPassification = _proofGenConfig.GenerateAstCfgProof
                ? beforeAstToCfgProgAccess
                : beforeCfgToDagProgAccess;

              var beforePassiveProgTheoryName =
                uniqueNamer.GetName(afterPassificationImpl.Name + "_before_passive_prog");
              var beforePassiveConfig =
                new IsaProgramGeneratorConfig(parentProgramAccessorForPassification, parentProgramAccessorForPassification == null, parentProgramAccessorForPassification == null, parentProgramAccessorForPassification == null, parentProgramAccessorForPassification == null,
                  SpecsConfig.None, false);
              beforePassiveProgAccess = new IsaProgramGenerator().GetIsaProgram(beforePassiveProgTheoryName,
                afterPassificationImpl.Name,
                mainData, beforePassiveConfig, varTranslationFactory2,
                beforePassificationCfg,
                uniqueNamer,
                out var programDeclsBeforePassive,
                CommandLineOptions.Clo.GenerateMembershipLemmas());

              var beforePassificationProgTheory = new Theory(beforePassiveProgTheoryName,
                new List<string> {"Boogie_Lang.Semantics", "Boogie_Lang.Util", theoryNameForParentImport},
                programDeclsBeforePassive);
              theories.Add(beforePassificationProgTheory);

              #endregion
            }
            
            if (_proofGenConfig.GeneratePassifiedProg)
            {
              #region after passification program

              //use global version map for translation 
              var fixedVarTranslation = new SimpleFixedVarTranslation(globalVersionMap);
              var fixedTyVarTranslation = new DeBruijnFixedTVarTranslation(finalProgData);
              varTranslationFactory =
                new DeBruijnVarFactory(fixedVarTranslation, fixedTyVarTranslation, boogieGlobalData);

              var finalProgTheoryName = uniqueNamer.GetName(afterPassificationImpl.Name + "_passive_prog");
              var passiveProgConfig =
                new IsaProgramGeneratorConfig(beforePassiveProgAccess, beforePassiveProgAccess==null, beforePassiveProgAccess==null, beforePassiveProgAccess==null, true, SpecsConfig.None, false);
              passiveProgAccess = new IsaProgramGenerator().GetIsaProgram(finalProgTheoryName,
                afterPassificationImpl.Name,
                finalProgData, passiveProgConfig, varTranslationFactory,
                //we use the CFG before the peep-hole transformations, so that we can directly use the VC to program proof in the passification phase
                afterPassificationCfg,
                uniqueNamer,
                out var programDecls,
                CommandLineOptions.Clo.GenerateMembershipLemmas());

              var afterPassificationProgTheory =
                new Theory(finalProgTheoryName,
                  new List<string>
                    {"Boogie_Lang.Semantics", "Boogie_Lang.Util", theoryNameForParentImport, beforePassiveProgAccess != null ? beforePassiveProgAccess.TheoryName() : ""},
                  programDecls);
              theories.Add(afterPassificationProgTheory);

              #endregion
            }

            var phasesTheories = new PhasesTheories(afterPassificationImpl.Name);
            Term vcAssm = null;
            LemmaDecl endToEndLemma = null;

            if (_proofGenConfig.GenerateVcProof)
            {
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

              var vcBoogieInfo = new VcBoogieInfo(vcinst, vcinstAxiom, vcAllAxioms, allAxiomsInfo);

              var vcProofData = new ProgramVcProofData(
                vcFunctions,
                vcBoogieInfo,
                vcHintManager,
                vcLocale,
                vcTranslator
              );

              #region VC phase proof

              var vcPhaseProofTheory = VcPhaseManager.ProgramToVcProof(
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
                uniqueNamer,
                out var vcAssmPrelim,
                out var endToEndLemmaPrelim
              );

              vcAssm = vcAssmPrelim;
              endToEndLemma = endToEndLemmaPrelim;
              
              theories.Add(vcPhaseProofTheory);

              #endregion
            }
            
            /*
            Console.WriteLine("Passive prog mapping: " + fixedVarTranslation.OutputMapping());
            Console.WriteLine("Before passive prog mapping: " + fixedVarTranslation2.OutputMapping());
            */

            if (_proofGenConfig.GeneratePassifProof)
            {
              #region passification proof

              IProgramAccessor beforePhaseProgramAccess = !_proofGenConfig.GenerateAstCfgProof
                ? beforePassiveProgAccess
                : beforeAstToCfgProgAccess;

              var passificationProofTheory = PassificationManager.PassificationProof(
                uniqueNamer.GetName(phasesTheories.TheoryName(PhasesTheories.Phase.Passification)),
                _proofGenConfig.GenerateVcProof ? phasesTheories.TheoryName(PhasesTheories.Phase.Vc) : "",
                _proofGenConfig.GeneratePassifE2E,
                endToEndLemma,
                vcAssm,
                beforePassificationCfg,
                beforePassiveToAfterPassiveBlock,
                passiveRelationGen,
                beforePhaseProgramAccess,
                beforePassiveProgAccess,
                passiveProgAccess,
                mainData,
                varTranslationFactory2,
                varTranslationFactory
              );
              theories.Add(passificationProofTheory);

              #endregion
            }

            if (_proofGenConfig.GenerateCfgDagProof)
            {
              #region cfg to dag

              var uniqueExitBlock =
                uniqueExitBlockOrig != null
                  ? beforePassiveOrigBlock.First(kv => kv.Value == uniqueExitBlockOrig).Key
                  : null;


              var cfgToDagProofTheory = CfgToDagManager.CfgToDagProof(
                phasesTheories,
                uniqueNamer,
                _proofGenConfig.GenerateCfgDagE2E,
                _proofGenConfig.GenerateAstCfgProof,
                _proofGenConfig.GeneratePassifProof,
                _proofGenConfig.GenerateVcProof,
                vcAssm,
                beforeDagCfg,
                beforePassificationCfg,
                uniqueExitBlock,
                beforeDagData,
                cfgToDagHintManager,
                beforeDagAfterDagBlock,
                beforeAstToCfgProgAccess,
                beforeCfgToDagProgAccess,
                beforePassiveProgAccess,
                varTranslationFactory2);
              theories.Add(cfgToDagProofTheory);

              #endregion
            }

            if (_proofGenConfig.GenerateAstCfgProof)
            {
              #region ast to cfg

              beforeCfgAfterCfgBlock = new Dictionary<BigBlock, Block>();
              IDictionary<BigBlock, (Block, Expr, BranchIndicator)> mappingWithHints =
                new Dictionary<BigBlock, (Block, Expr, BranchIndicator)>();

              //IDictionary<BigBlock, BigBlock> mappingCopyBigblockToOrigBigblock =
              //proofGenInfo.GetMappingCopyBigblockToOrigBigblock();
              IDictionary<BigBlock, Block> mappingOrigBigBlockToOrigBlock =
                proofGenInfo.GetMappingOrigBigBlockToOrigBlock();

              IDictionary<Block, Block> mappingOrigBlockToUnoptimizedCopy =
                proofGenInfo.GetMappingOrigBlockToUnoptimizedCopy();
              IDictionary<Block, Block> mappingUnoptimizedCopyToOrigBlock =
                mappingOrigBlockToUnoptimizedCopy.InverseDict();

              IDictionary<Block, Block> mappingOrigBlockToCopyBlock = beforeDagOrigBlock.InverseDict();

              IDictionary<BigBlock, (Expr, BranchIndicator)> mappingBigBlockToHints =
                proofGenInfo.GetMappingCopyBigBlockToHints();
              foreach (var pair in mappingOrigBigBlockToOrigBlock)
              {
                var origBigBlock = pair.Key;
                var copyBigBlock = proofGenInfo.GetMappingOrigBigblockToCopyBigblock()[origBigBlock];
                var origBlock = pair.Value;

                var blockToBlockMapToReferTo = proofGenInfo.GetOptimizationsFlag()
                  ? mappingOrigBlockToUnoptimizedCopy
                  : mappingOrigBlockToCopyBlock;

                var copyBlock = blockToBlockMapToReferTo[origBlock];
                var hints = mappingBigBlockToHints[origBigBlock];

                beforeCfgAfterCfgBlock.Add(copyBigBlock, copyBlock);
                mappingWithHints.Add(copyBigBlock, (copyBlock, hints.Item1, hints.Item2));
              }

              CFGRepr astCfgReprInput;
              BoogieMethodData astCfgDataInput;
              IDictionary<Block, Block> blockToBlockMapInput;
              IProgramAccessor beforeCfgToDagProgAccessInput;

              if (!proofGenInfo.GetOptimizationsFlag())
              {
                astCfgReprInput = beforeDagCfg;
                astCfgDataInput = beforeDagData;
                blockToBlockMapInput = beforeDagOrigBlock;
                beforeCfgToDagProgAccessInput = beforeCfgToDagProgAccess;

              }
              else
              {
                astCfgReprInput = beforeOptimizationsCFG;
                astCfgDataInput = beforeOptimizationsData;
                blockToBlockMapInput = mappingUnoptimizedCopyToOrigBlock;
                beforeCfgToDagProgAccessInput = unoptimizedCfgProgAccess;
              }

              var astToCfgProofTheory = AstToCfgManager.AstToCfgProof(
                uniqueNamer.GetName(phasesTheories.TheoryName(PhasesTheories.Phase.AstToCfg)),
                phasesTheories,
                _proofGenConfig.GenerateAstCfgE2E,
                _proofGenConfig,
                vcAssm,
                proofGenInfo,
                beforeCfgAst,
                astCfgReprInput,
                astCfgDataInput,
                blockToBlockMapInput,
                mappingWithHints,
                beforeCfgAfterCfgBlock,
                beforeAstToCfgProgAccess,
                beforeCfgToDagProgAccessInput,
                varTranslationFactory2,
                cmdIsaVisitor);
              theories.Add(astToCfgProofTheory);

              #endregion
            }

            StoreResult(uniqueNamer.GetName(afterPassificationImpl.Proc.Name), theories);
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