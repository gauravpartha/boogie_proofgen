using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using System.Text;
using Isabelle.Ast;
using Isabelle.Util;
using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.BoogieIsaInterface.VariableTranslation;
using ProofGeneration.CFGRepresentation;
using ProofGeneration.Util;

namespace ProofGeneration.AstToCfg
{
    public class AstToCfgLemmaManager
    {
        private readonly CFGRepr afterCfg;
        private readonly IProgramAccessor afterCfgProgAccess;

        private readonly BasicCmdIsaVisitor basicCmdIsaVisitor;

        private readonly IProgramAccessor beforeCfgProgAccess;
        private readonly IDictionary<BigBlock, Block> beforeToAfterBlock;
        
        private readonly BoogieContextIsa astBoogieContext;
        private readonly BoogieContextIsa cfgBoogieContext;
        
        private readonly TermIdent finalNode = IsaCommonTerms.TermIdentFromName("m'");
        private readonly Term finalState = IsaCommonTerms.TermIdentFromName("s'");
        private readonly string funContextWfName;

        private readonly IDictionary<BigBlock, LemmaDecl> mappingBigBlockToGlobalLemmaDecl;
        private readonly IDictionary<BigBlock, LemmaDecl> mappingBigBlockToLocalLemmaDecl;

        //private readonly CfgToDagHintManager hintManager;

        private readonly IsaUniqueNamer namer = new IsaUniqueNamer();
        
        private readonly Term initState1;
        private readonly Term normalInitState1 = IsaCommonTerms.TermIdentFromName("ns1");

        private readonly string redCfgName = "Red";

        //private readonly TypingTacticGenerator typingTacticGenerator;
        private readonly IVariableTranslation<Variable> variableTranslation;

        private readonly BoogieMethodData beforeCfgData;

        private readonly IDictionary<Block, Block> beforeDagOrigBlock;

        public AstToCfgLemmaManager(
            IProgramAccessor beforeCfgProgAccess,
            IProgramAccessor afterCfgProgAccess,
            BoogieContextIsa astBoogieContext,
            BoogieContextIsa cfgBoogieContext,
            CFGRepr afterCfg,
            string funContextWfName,
            // CfgToDagHintManager hintManager,
            // IDictionary<Block, IList<Block>> blocksToLoops,
            IDictionary<Block, Block> beforeDagOrigBlock,
            IDictionary<BigBlock, Block> beforeToAfterBlock,
            BoogieMethodData beforeCfgData,
            IVariableTranslationFactory varFactory
        )
        {
            this.beforeCfgProgAccess = beforeCfgProgAccess;
            this.afterCfgProgAccess = afterCfgProgAccess;
            this.afterCfg = afterCfg;
            this.funContextWfName = funContextWfName;
            variableTranslation = varFactory.CreateTranslation().VarTranslation;
            // this.hintManager = hintManager;
            // this.blocksToLoops = blocksToLoops;
            this.beforeToAfterBlock = beforeToAfterBlock;
            this.beforeCfgData = beforeCfgData;
            
            this.astBoogieContext = astBoogieContext;
            this.cfgBoogieContext = cfgBoogieContext;
            
            initState1 = IsaBoogieTerm.Normal(normalInitState1);
            basicCmdIsaVisitor = new BasicCmdIsaVisitor(varFactory);
            mappingBigBlockToGlobalLemmaDecl = new Dictionary<BigBlock, LemmaDecl>();
            mappingBigBlockToLocalLemmaDecl = new Dictionary<BigBlock, LemmaDecl>();
            //typingTacticGenerator = new TypingTacticGenerator(beforeCfgProgAccess, varFactory);

            this.beforeDagOrigBlock = beforeDagOrigBlock;
        }

        private TermList HavocedVarsTerm(IEnumerable<Variable> vars)
        {
            return new TermList(
                vars.Select(x =>
                {
                    if (variableTranslation.TryTranslateVariableId(x, out var varId, out _))
                    {
                      return varId;
                    }

                    throw new ProofGenUnexpectedStateException("Could not extract variable id");
                }).ToList());
        }
        private Term InvariantsTerm(IEnumerable<Expr> invs)
        {
          return new TermList(invs.Select(e => basicCmdIsaVisitor.Translate(e)).ToList());
        }
        private Term ExprTerm(Expr expr)
        {
          return basicCmdIsaVisitor.Translate(expr);
        }

        public LemmaDecl LocalLemma(
            BigBlock beforeBlock,
            Block afterBlock,
            Expr guardHint,
            Func<BigBlock, string> blockLemmaName,
            BranchIndicator indicator)
        {
            var beforeBigblockDefName = beforeCfgProgAccess.BigBlockInfo().CmdsQualifiedName(beforeBlock).First();
            Term startConfig = IsaBoogieTerm.StartConfigTerm(beforeBlock, IsaCommonTerms.TermIdentFromName("cont0"), beforeCfgProgAccess, initState1);
            Term endConfig = IsaBoogieTerm.EndConfigTerm();

            var afterCmdsDefName = afterCfgProgAccess.BlockInfo().CmdsQualifiedName(afterBlock);
            Term afterCmds = IsaCommonTerms.TermIdentFromName(afterCmdsDefName);

            var quatifiedstateId = new SimpleIdentifier("ns1'");
            
            var finalStateId2 = new SimpleIdentifier("s2'");
            Term finalState2 = new TermIdent(finalStateId2);
            Term astId = IsaBoogieTerm.astId();

            var localLemmas = new List<LemmaDecl>();

            #region local block lemma

            //TODO: write the proofs using ProofUtil
            var assumptions = new List<Term>
            {
                IsaBoogieTerm.RedBigBlock(astBoogieContext, startConfig, endConfig, astId)
            };

            Term cfgVerifiesAssm =
                TermQuantifier.MetaAll(
                    new List<Identifier> {finalStateId2},
                    null,
                    TermBinary.MetaImplies(
                        IsaBoogieTerm.RedCmdList(cfgBoogieContext, afterCmds, initState1, finalState2),
                        TermBinary.Neq(finalState2, IsaBoogieTerm.Failure()))
                );
            assumptions.Add(cfgVerifiesAssm);

            bool hasGuardHint = false;
            if (indicator == BranchIndicator.GuardHolds && guardHint != null)
            {
              Term traceIsPossible = IsaBoogieTerm.RedExpr(astBoogieContext,
                ExprTerm(guardHint),
                normalInitState1,
                new TermApp(IsaBoogieTerm.BoolValConstr(), IsaCommonTerms.TermIdentFromName("True")));
              hasGuardHint = true;
              assumptions.Add(traceIsPossible);
            }
            else if (indicator == BranchIndicator.GuardFails && guardHint != null)
            {
              Term traceIsPossible = IsaBoogieTerm.RedExpr(astBoogieContext,
                ExprTerm(guardHint),
                normalInitState1,
                new TermApp(IsaBoogieTerm.BoolValConstr(), IsaCommonTerms.TermIdentFromName("False")));
              hasGuardHint = true;
              assumptions.Add(traceIsPossible);
            }

            Term conclusion =
                TermBinary.And(
                  TermBinary.Neq(IsaCommonTerms.TermIdentFromName("reached_state"), IsaBoogieTerm.Failure()), 
                  TermQuantifier.ForAll(
                    new List<Identifier> {quatifiedstateId},
                    null,
                    TermBinary.Implies(
                      TermBinary.Eq(IsaCommonTerms.TermIdentFromName("reached_state"), IsaBoogieTerm.Normal(new TermIdent(quatifiedstateId))), 
                      IsaBoogieTerm.RedCmdList(cfgBoogieContext, afterCmds, initState1, IsaBoogieTerm.Normal(new TermIdent(quatifiedstateId))) )
                    ));

            var proofMethods = new List<string>();
            var proofSb = new StringBuilder();
            
            if (indicator == 0 || guardHint == null)
            {
              proofSb.AppendLine(ProofUtil.Apply("rule block_local_rel_generic"));
              proofSb.AppendLine(ProofUtil.Apply("rule Rel_Main_test[of " + beforeBigblockDefName + "]"));
              proofSb.AppendLine(ProofUtil.Apply("simp add: " + beforeBigblockDefName + "_def " + afterCmdsDefName + "_def"));
              proofSb.AppendLine(ProofUtil.Apply(ProofUtil.Repeat("simp add: " + afterCmdsDefName + "_def")));
              proofSb.AppendLine(ProofUtil.Apply("rule astStep"));
              proofSb.AppendLine(ProofUtil.Apply("rule cfgBlockDoesntFail"));
              proofSb.AppendLine(ProofUtil.Apply( ProofUtil.Repeat("simp add: " + afterCmdsDefName + "_def " + beforeBigblockDefName + "_def")));
              proofSb.AppendLine("done");
              
              // proofMethods = new List<string>
              // {
              //   ProofUtil.Apply("rule block_local_rel_generic"),
              //   ProofUtil.Apply("rule Rel_Main_test[of " + beforeBigblockDefName + "]"),
              //   ProofUtil.Apply("simp add: " + beforeBigblockDefName + "_def " + afterCmdsDefName + "_def"),
              //   ProofUtil.Apply("simp add: " + afterCmdsDefName + "_def)+",
              //   ProofUtil.Apply("rule astStep"),
              //   ProofUtil.Apply("rule cfgBlockDoesntFail"),
              //   ProofUtil.Apply("simp add: " + afterCmdsDefName + "_def " + beforeBigblockDefName + "_def)+",
              //   "done"
              // };
            } 
            else if (indicator == BranchIndicator.GuardHolds)
            {
              proofSb.AppendLine("unfolding " + afterCmdsDefName + "_def");
              proofSb.AppendLine(ProofUtil.Apply("rule guard_holds_push_through_assumption"));
              proofSb.AppendLine(ProofUtil.Apply("rule block_local_rel_generic"));
              proofSb.AppendLine(ProofUtil.Apply("rule Rel_Main_test[of " + beforeBigblockDefName + "]"));
              proofSb.AppendLine(ProofUtil.Apply("simp add: " + beforeBigblockDefName + "_def"));
              proofSb.AppendLine(ProofUtil.Apply("simp+"));
              proofSb.AppendLine(ProofUtil.Apply("rule astStep"));
              proofSb.AppendLine(ProofUtil.Apply("rule push_through_assumption_test1, rule cfgBlockDoesntFail"));
              proofSb.AppendLine(ProofUtil.Apply("simp add: " + afterCmdsDefName + "_def"));
              proofSb.AppendLine(ProofUtil.Apply(ProofUtil.Repeat("simp add: assms(3) " + beforeBigblockDefName + "_def")));
              proofSb.AppendLine("done");
                
              // proofMethods = new List<string>
              // {
              //   "unfolding " + afterCmdsDefName + "_def",
              //   ProofUtil.Apply("rule guard_holds_push_through_assumption"),
              //   ProofUtil.Apply("rule block_local_rel_generic"),
              //   ProofUtil.Apply("rule Rel_Main_test[of " + beforeBigblockDefName + "]"),
              //   ProofUtil.Apply("simp add: " + beforeBigblockDefName + "_def"),
              //   ProofUtil.Apply(ProofUtil.Repeat(ProofUtil.Simp())),
              //   ProofUtil.Apply("rule astStep"),
              //   ProofUtil.Apply("rule push_through_assumption_test1, rule cfgBlockDoesntFail"),
              //   ProofUtil.Apply("simp add: " + afterCmdsDefName + "_def"),
              //   ProofUtil.Apply("simp add: assms(3) " + beforeBigblockDefName + "_def)+",
              //   "done"
              // };
            }
            else if (indicator ==  BranchIndicator.GuardFails)
            {
              proofSb.AppendLine("unfolding " + afterCmdsDefName + "_def");
              proofSb.AppendLine(ProofUtil.Apply("rule guard_fails_push_through_assumption"));
              proofSb.AppendLine(ProofUtil.Apply("rule block_local_rel_generic"));
              proofSb.AppendLine(ProofUtil.Apply("rule Rel_Main_test[of " + beforeBigblockDefName + "]"));
              proofSb.AppendLine(ProofUtil.Apply("simp add: " + beforeBigblockDefName + "_def"));
              proofSb.AppendLine(ProofUtil.Apply("simp+"));
              proofSb.AppendLine(ProofUtil.Apply("rule astStep"));
              proofSb.AppendLine(ProofUtil.Apply("rule cfgBlockDoesntFail"));
              proofSb.AppendLine(ProofUtil.Apply("simp add: " + afterCmdsDefName + "_def"));
              proofSb.AppendLine(ProofUtil.Apply("rule push_through_assumption1"));
              proofSb.AppendLine(ProofUtil.Apply("simp"));
              proofSb.AppendLine(ProofUtil.Apply(NegationRule(guardHint)));
              proofSb.AppendLine(ProofUtil.Apply("rule guardHint"));
              proofSb.AppendLine(ProofUtil.Apply( ProofUtil.Repeat("simp add: " + beforeBigblockDefName + "_def")));
              proofSb.AppendLine(ProofUtil.Apply(NegationRule(guardHint)));
              proofSb.AppendLine(ProofUtil.Apply("rule guardHint"));
              proofSb.AppendLine("done");
              
              // proofMethods = new List<string>
              // {
              //   "unfolding " + afterCmdsDefName + "_def",
              //   ProofUtil.Apply("rule guard_fails_push_through_assumption"),
              //   ProofUtil.Apply("rule block_local_rel_generic"),
              //   ProofUtil.Apply("rule Rel_Main_test[of " + beforeBigblockDefName + "]"),
              //   ProofUtil.Apply("simp add: " + beforeBigblockDefName + "_def"),
              //   ProofUtil.Apply(ProofUtil.Repeat(ProofUtil.Simp())),
              //   ProofUtil.Apply("rule astStep"),
              //   ProofUtil.Apply("rule cfgBlockDoesntFail"),
              //   ProofUtil.Apply("simp add: " + afterCmdsDefName + "_def"),
              //   ProofUtil.Apply("rule push_through_assumption1"),
              //   ProofUtil.Apply(ProofUtil.Simp()),
              //   ProofUtil.Apply("" + NegationRule(guardHint) + ""),
              //   ProofUtil.Apply("rule guardHint"),
              //   ProofUtil.Apply("simp add: " + beforeBigblockDefName + "_def)+",
              //   ProofUtil.Apply("" + NegationRule(guardHint) + ""),
              //   ProofUtil.Apply("rule guardHint"),
              //   "done"
              // };
            }

            List<string> assmsLabels = new List<string> {"astStep", "cfgBlockDoesntFail"};
            if (hasGuardHint)
            {
              assmsLabels.Add("guardHint");
            }
            var localLemma = new LemmaDecl(
                blockLemmaName(beforeBlock),
                ContextElem.CreateWithAssumptions(assumptions, assmsLabels),
                conclusion,
                new Proof(new List<string> {proofSb.ToString()})
            );

            #endregion

            mappingBigBlockToLocalLemmaDecl.Add(beforeBlock, localLemma);
            localLemmas.Add(localLemma);

            return localLemma;
        }

        #region generate global lemma
        public LemmaDecl GenerateGlobalLemma(
          BigBlock startingBigBlock,
          Term continuation, 
          Block relatedBlock, 
          Term posts,
          (Expr, BranchIndicator) hints,
          Func<BigBlock, string> globalBlockLemmaName,
          ProofGenInfo proofGenInfo)
        {
          var assumptions = new List<Term>();

          #region assumption 1: trace through the ast
          Term startConfig = IsaBoogieTerm.StartConfigTerm(startingBigBlock, continuation, beforeCfgProgAccess, initState1);
          Term endConfig = IsaBoogieTerm.EndConfigTerm();
          Term astId = IsaBoogieTerm.astId();
          Term numStepsId = IsaCommonTerms.TermIdentFromName("j");

          Term astTrace = IsaBoogieTerm.RedBigBlockKStep(astBoogieContext, startConfig, endConfig, astId, numStepsId);
          assumptions.Add(astTrace);
          #endregion
          
          var finalCfgNodeId = new SimpleIdentifier("m'");
          var finalStateId = new SimpleIdentifier("s'");
          Term initialStateNode = new NatConst(afterCfg.GetUniqueIntLabel(relatedBlock));
          var boundStateId = new SimpleIdentifier("ns_end");

          #region assumption 2: all cfg traces end in a non-failing state
          
          Term cfgVerifiesAssm =
            TermQuantifier.MetaAll(
              new List<Identifier> {finalCfgNodeId, finalStateId},
              null,
              TermBinary.MetaImplies(
                IsaBoogieTerm.RedCFGMulti(cfgBoogieContext,
                  afterCfgProgAccess.CfgDecl(),
                  IsaBoogieTerm.CFGConfigNode(
                    initialStateNode, IsaBoogieTerm.Normal(normalInitState1)
                  ),
                  IsaBoogieTerm.CFGConfig(finalNode, finalState)),
                TermBinary.Neq(finalState, IsaBoogieTerm.Failure()))
            );
          assumptions.Add(cfgVerifiesAssm);
          
          #endregion

          #region assumption 3: all cfg traces end in a state that satisfies the post-conditions
          Term cfgSatisfiesPostsAssm =
            TermQuantifier.MetaAll(
              new List<Identifier> {finalCfgNodeId, finalStateId},
              null,
              TermBinary.MetaImplies(
                IsaBoogieTerm.RedCFGMulti(cfgBoogieContext,
                  afterCfgProgAccess.CfgDecl(),
                  IsaBoogieTerm.CFGConfigNode(
                    initialStateNode, IsaBoogieTerm.Normal(normalInitState1)
                  ),
                  IsaBoogieTerm.CFGConfig(finalNode, finalState)),
                TermBinary.MetaImplies(  
                  new TermApp(IsaCommonTerms.TermIdentFromName("is_final_config"), IsaBoogieTerm.CFGConfig(finalNode, finalState)),
                  TermQuantifier.ForAll(
                    new List<Identifier> {boundStateId},
                    null,
                    TermBinary.Implies(
                      TermBinary.Eq(finalState, IsaBoogieTerm.Normal(new TermIdent(boundStateId))), 
                      IsaBoogieTerm.ExprAllSat(astBoogieContext, new TermIdent(boundStateId), posts))
                  )
                ))
            );
          assumptions.Add(cfgSatisfiesPostsAssm);
          
          #endregion

          #region conditional assumption 4: the given trace through the ast is actually possible

          bool guardSemantics = false;
          BigBlock correspondingOrigBigBlock = proofGenInfo.GetMappingCopyBigblockToOrigBigblock()[startingBigBlock];
          if (hints.Item2 == BranchIndicator.GuardHolds && hints.Item1 != null)
          {
            Term traceIsPossible = IsaBoogieTerm.RedExpr(astBoogieContext,
              ExprTerm(hints.Item1),
              normalInitState1,
              new TermApp(IsaBoogieTerm.BoolValConstr(), IsaCommonTerms.TermIdentFromName("True")));
            guardSemantics = true;
            assumptions.Add(traceIsPossible);
          }
          else if (hints.Item2 == BranchIndicator.GuardFails && hints.Item1 != null)
          {
            Term traceIsPossible = IsaBoogieTerm.RedExpr(astBoogieContext,
              ExprTerm(hints.Item1),
              normalInitState1,
              new TermApp(IsaBoogieTerm.BoolValConstr(), IsaCommonTerms.TermIdentFromName("False")));
            guardSemantics = true;
            assumptions.Add(traceIsPossible);
          }
          else if (proofGenInfo.GetMappingCopyBigblockToOrigBigblockWithTupleValue().ContainsKey(startingBigBlock))
          {
            WhileCmd wcmd = (WhileCmd) startingBigBlock.ec;
            if (wcmd.Guard == null)
            {
              Term personalGuard = Isabelle.Util.IsaCommonTerms.TermIdentFromName("personal_guard");
              Term equalitySign = Isabelle.Util.IsaCommonTerms.TermIdentFromName("=");

              Term personalGuardIsNone =
                new TermApp(personalGuard, equalitySign, IsaCommonTerms.NoneOption());
              guardSemantics = true;
              assumptions.Add(personalGuardIsNone);
            }
          } 
          else if (proofGenInfo.GetMappingBigBlockToLoopBigBlock().ContainsKey(correspondingOrigBigBlock))
          {
            BigBlock loopBigBlockOrig = proofGenInfo.GetMappingBigBlockToLoopBigBlock()[correspondingOrigBigBlock];
            BigBlock loopBigBlockCopy = proofGenInfo.GetMappingOrigBigblockToCopyBigblock()[loopBigBlockOrig];

            WhileCmd wcmd = (WhileCmd) loopBigBlockCopy.ec;
            if (wcmd.Guard == null)
            {
              Term enclosingLoopGuard = Isabelle.Util.IsaCommonTerms.TermIdentFromName("guard_of_enclosing_loop");
              Term equalitySign = Isabelle.Util.IsaCommonTerms.TermIdentFromName("=");

              Term enclosingLoopGuardIsNone =
                new TermApp(enclosingLoopGuard, equalitySign, IsaCommonTerms.NoneOption());
              guardSemantics = true;
              assumptions.Add(enclosingLoopGuardIsNone);
            }
          }

          #endregion
          
          BigBlock correspondingBigBlockOrig = proofGenInfo.GetMappingCopyBigblockToOrigBigblock()[startingBigBlock];
          if (proofGenInfo.GetMappingCopyBigblockToOrigBigblockWithTupleValue().ContainsKey(startingBigBlock))
          {
            correspondingBigBlockOrig = proofGenInfo.GetMappingCopyBigblockToOrigBigblockWithTupleValue()[startingBigBlock].Item2;
          }
          BigBlock successorBigBlockOrig = correspondingBigBlockOrig.successorBigBlock;

          #region conditional assumption 5: loop induction hypothesis

          bool hasLoopIH = false;
          if (proofGenInfo.GetMappingBigBlockToLoopBigBlock().ContainsKey(correspondingBigBlockOrig))
          {
            BigBlock enclosingLoop = proofGenInfo.GetMappingBigBlockToLoopBigBlock()[correspondingBigBlockOrig];
            BigBlock enclosingLoopCopy = proofGenInfo.GetMappingOrigBigblockToCopyBigblock()[enclosingLoop];

            IDictionary<Block, Block> origBlockBeforeDag = beforeDagOrigBlock.InverseDict();
            Block enclosingLoopCfgBlock = proofGenInfo.GetMappingOrigBigBlockToOrigBlock()[enclosingLoop];
            Block enclosingLoopCfgBlockCopy = origBlockBeforeDag[enclosingLoopCfgBlock];

            Term blockIndex;
            if (true /* enclosingLoopCfgBlockCopy.cmds.Any() */ )
            {
              Block successorCfgBlock = afterCfg.GetSuccessorBlocks(enclosingLoopCfgBlockCopy).First();
              //Block successorCfgBlockCopy = origBlockBeforeDag[successorCfgBlock];
              
              blockIndex = new NatConst(afterCfg.GetUniqueIntLabel(successorCfgBlock));
            }
            else
            {
              blockIndex = new NatConst(afterCfg.GetUniqueIntLabel(enclosingLoopCfgBlockCopy));
            }
            
            int unwrappedEnclosingLoopBigBlockIndex = proofGenInfo.GetMappingCopyBigBlockToIndex()[enclosingLoopCopy] + 1;

            Term succBigBlockTermId = IsaCommonTerms.TermIdentFromName(beforeCfgProgAccess.BigBlockInfo().TheoryName + ".bigblock_" + unwrappedEnclosingLoopBigBlockIndex);
            Term succContId = IsaCommonTerms.TermIdentFromName("cont_" + unwrappedEnclosingLoopBigBlockIndex);
            Term cfgBodyId = IsaCommonTerms.TermIdentFromName(afterCfgProgAccess.BlockInfo().getTheoryName() + ".proc_body");
            //Term blockIndex = new NatConst(unwrappedEnclosingLoopBigBlockIndex);

            Term loop_ih_assm = IsaBoogieTerm.LoopIH(astBoogieContext, cfgBoogieContext, astId, succBigBlockTermId, succContId, cfgBodyId, blockIndex, posts);
            hasLoopIH = true;
            assumptions.Add(loop_ih_assm);
          }

          #endregion
          
          Term conclusion = IsaBoogieTerm.AstValidConfiguration(astBoogieContext, posts);

          //TODO: Document the cases for the proofs
          #region proof
          var proofMethods = new List<string>();
          
          //A BigBlock is final if it EITHER has no successor and it has no structure to branch into OR it contains a return command. 
          if (successorBigBlockOrig == null && startingBigBlock.ec == null || startingBigBlock.tc is ReturnCmd)
          {
            proofMethods = GenerateFinalBlockProof(startingBigBlock, relatedBlock, hints.Item1, hints.Item2, proofGenInfo);
          }
          //TODO: Fix this.
          //A BigBlock is a LoopHead if it is a key in this dictionary.
          else if (proofGenInfo.GetMappingCopyBigblockToOrigBigblockWithTupleValue().ContainsKey(startingBigBlock))
          {
            WhileCmd wcmd = (WhileCmd) startingBigBlock.ec;
            Expr guard = wcmd.Guard;
            proofMethods = GenerateLoopHeadProof(startingBigBlock, relatedBlock, guard, proofGenInfo);
          }
          //A BigBlock is generic if it has no structure to branch into and it doesn't contain a return command.
          else if (startingBigBlock.ec == null)
          {
            proofMethods = GenerateProofGeneric(startingBigBlock, relatedBlock, hints.Item1, hints.Item2, proofGenInfo);
          }
          //A 'WhileSuccessor' proof is generated for a BigBlock that contains a non-null WhileCmd object and a non-empty simpleCmds list.
          //A BigBlock that contains a non-null WhileCmd object and an empty simpleCmds list is treated as a special case.
          else if (startingBigBlock.ec is WhileCmd && mappingBigBlockToLocalLemmaDecl.ContainsKey(startingBigBlock))
          {
            WhileCmd wcmd = (WhileCmd) startingBigBlock.ec;
            Expr personalGuard = wcmd.Guard;
            proofMethods = GenerateWhileSuccessorProof(startingBigBlock, relatedBlock, hints.Item1, personalGuard, hints.Item2, proofGenInfo);
          }
          //An 'IfSuccessor' proof is generated for a BigBlock that contains a non-null IfCmd object.
          else if (startingBigBlock.ec is IfCmd)
          {
            IfCmd ifcmd = (IfCmd) startingBigBlock.ec;
            Expr guard = ifcmd.Guard;
            proofMethods = GenerateIfSuccessorProof(startingBigBlock, relatedBlock, guard, hints.Item1, hints.Item2, proofGenInfo);
          }
          //TODO: Test consecutive loops in a loop.
          /* TODO: All BigBlocks in a loop body except the very first one are assigned a NoGuard BranchIndicator.
             TODO: This works for ProofGen only if Block Coalescing is turned off. */
          //These last three checks all address the special case of a BigBlock that contains a non-null WhileCmd object and an empty simpleCmds.
          //1. The BigBlock contains a non-null WhileCmd object and an empty simpleCmds and is right in the beginning of an Else Branch.
          else if (hints.Item2 == BranchIndicator.GuardFails && 
                   correspondingBigBlockOrig.ec is WhileCmd && 
                   !startingBigBlock.simpleCmds.Any())
          {
            proofMethods = GenerateEndingAfterUnwrappingProof(startingBigBlock, relatedBlock, hints.Item1, BranchIndicator.GuardFails, proofGenInfo);
          }
          //2. The BigBlock contains a non-null WhileCmd object and an empty simpleCmds and is in another loop.
          else if (proofGenInfo.GetMappingBigBlockToLoopBigBlock().ContainsKey(correspondingBigBlockOrig))
          {
            proofMethods = GenerateEndingAfterUnwrappingProof(startingBigBlock, relatedBlock, hints.Item1, hints.Item2, proofGenInfo);
          }
          //3. The BigBlock contains a non-null WhileCmd object and an empty simpleCmds. 
          else if (!startingBigBlock.simpleCmds.Any() && startingBigBlock.ec is WhileCmd)
          {
            proofMethods = GenerateEndingAfterUnwrappingProof(startingBigBlock, relatedBlock, hints.Item1, BranchIndicator.NoGuard, proofGenInfo);
          }
          #endregion

          List<string> assmsLabels = new List<string> {"astTrace", "cfgDoesntFail", "cfgSatisfiesPosts"};
          if (guardSemantics)
          {
            assmsLabels.Add("guardHint");
          }

          if (hasLoopIH)
          {
            assmsLabels.Add("inductionHypothesis");
          }
          
          var globalLemma = new LemmaDecl(
            globalBlockLemmaName(startingBigBlock),
            ContextElem.CreateWithAssumptions(assumptions, assmsLabels),
            conclusion,
            new Proof(proofMethods)
          );
          
          mappingBigBlockToGlobalLemmaDecl.Add(startingBigBlock, globalLemma);
          return globalLemma;
        }
        #endregion

        private string NegationRule(Expr guard)
        {
          NAryExpr nary = guard as NAryExpr;

          if (ReferenceEquals(guard, Expr.Literal(true)))
          {
            return ProofUtil.Rule("neg_equiv1");
          }
          if (ReferenceEquals(guard, Expr.Literal(false)))
          {
            return ProofUtil.Rule("neg_equiv2");
          }
          if (nary != null)
          {
            if (nary.Fun is UnaryOperator unOp)
            {
              if (unOp.Op == UnaryOperator.Opcode.Not)
              {
                return ProofUtil.Rule("double_neg");
              }
            }
            else if (nary.Fun is BinaryOperator binOp)
            {
              if (binOp.Op == BinaryOperator.Opcode.Eq)
              {
                return ProofUtil.Rule("neg_eq");
              }
              if (binOp.Op == BinaryOperator.Opcode.Neq)
              {
                return ProofUtil.Rule("neg_neq");
              }
              if (binOp.Op == BinaryOperator.Opcode.Lt)
              {
                return ProofUtil.Rule("neg_lt");
              }
              if (binOp.Op == BinaryOperator.Opcode.Le)
              {
                return ProofUtil.Rule("neg_le");
              }
              if (binOp.Op == BinaryOperator.Opcode.Ge)
              {
                return ProofUtil.Rule("neg_ge");
              }
              if (binOp.Op == BinaryOperator.Opcode.Gt)
              {
                return ProofUtil.Rule("neg_gt");
              }
            }
          }

          return ProofUtil.Rule("neg_refl");
        }

        private string ExpandDefinitions(string contId, BigBlock startingBigBlock, ProofGenInfo proofGenInfo, BranchIndicator branchIndicator)
        {
          //BigBlock correspondingBigBlockOrig = proofGenInfo.getMappingCopyBigblockToOrigBigblock()[startingBigBlock];
          //IfCmd _if = (IfCmd) correspondingBigBlockOrig.ec;
          
          IfCmd @if = (IfCmd) startingBigBlock.ec;

          string expansion = "apply (simp add: " + contId + "_def ";
          if (branchIndicator == BranchIndicator.GuardHolds)
          {
            foreach (var thenBb in @if.thn.BigBlocks)
            {
              BigBlock thenBranchCopy = thenBb;  //proofGenInfo.getMappingOrigBigblockToCopyBigblock()[then_bb];
              string thenBranchId = beforeCfgProgAccess.BigBlockInfo().CmdsQualifiedName(thenBranchCopy).First();
              string thenBranchContId = "cont_" + (proofGenInfo.GetMappingCopyBigBlockToIndex()[thenBranchCopy]);
              expansion += thenBranchId + "_def " + thenBranchContId + "_def ";
            }
          }
          else if (@if.elseBlock != null)
          {
            foreach (var elseBb in @if.elseBlock.BigBlocks)
            {
              BigBlock elseBranchCopy = elseBb; //proofGenInfo.getMappingOrigBigblockToCopyBigblock()[else_bb];
              string elseBranchId = beforeCfgProgAccess.BigBlockInfo().CmdsQualifiedName(elseBranchCopy).First();
              string elseBranchContId = "cont_" + (proofGenInfo.GetMappingCopyBigBlockToIndex()[elseBranchCopy]);
              expansion += elseBranchId + "_def " + elseBranchContId + "_def ";
            }
          }

          expansion += ")";
          return expansion;
        }
        
        private List<string> GenerateFinalBlockProof( 
          BigBlock startingBigBlock,
          Block relatedBlock,
          Expr entryGuard,
          BranchIndicator indicator,
          ProofGenInfo proofGenInfo)
        {
          string bigblockId = beforeCfgProgAccess.BigBlockInfo().CmdsQualifiedName(startingBigBlock).First();
          string blockId = afterCfgProgAccess.BlockInfo().getTheoryName() + ".block_" + afterCfg.GetUniqueIntLabel(relatedBlock);
          string nodeId = afterCfgProgAccess.BlockInfo().getTheoryName() + ".node_" + afterCfg.GetUniqueIntLabel(relatedBlock);
          string outEdgesId = afterCfgProgAccess.BlockInfo().getTheoryName() + ".outEdges_" + afterCfg.GetUniqueIntLabel(relatedBlock);
          string contId = "cont_" + proofGenInfo.GetMappingCopyBigBlockToIndex()[startingBigBlock];

          string syntacticRel;
          string traceIsPossible = ProofUtil.Apply("rule guardHint"); 
          List<string> finalPartofProof;
          List<string> middlePartofProof;
          List<string> beginningOfProof;
          
          if (mappingBigBlockToLocalLemmaDecl.ContainsKey(startingBigBlock))
          {
            string nameLemmaLocal = "placeholder";
            if (mappingBigBlockToLocalLemmaDecl.ContainsKey(startingBigBlock))
            {
              nameLemmaLocal = mappingBigBlockToLocalLemmaDecl[startingBigBlock].Name;
            }
            
            syntacticRel =  ProofUtil.Apply("rule Rel_Main_test[of " + bigblockId + "]");
            finalPartofProof = new List<string>
            {
              ProofUtil.Apply("rule " + nameLemmaLocal),
              "apply assumption+",
              (indicator != 0 && entryGuard != null) ? traceIsPossible : "",
              "done",
              "qed"
            };
          }
          else if (startingBigBlock.tc is ReturnCmd)
          {
            syntacticRel = ProofUtil.Apply("rule Rel_Invs[of " + bigblockId + "]");
            finalPartofProof = new List<string>
            {
              ProofUtil.Apply("simp add: " + bigblockId + "_def"),
              ProofUtil.Apply("simp add: " + blockId + "_def"),
              ProofUtil.Apply("simp add: end_return"),
              "done",
              "qed"
            };
          }
          else
          {
            syntacticRel = ProofUtil.Apply("rule Rel_Invs[of " + bigblockId + "]");
            finalPartofProof = new List<string>
            {
              ProofUtil.Apply("simp add: " + bigblockId + "_def"),
              ProofUtil.Apply("simp add: end_static"),
              "done",
              "qed"
            };
          }

          if (indicator == 0 || entryGuard == null)
          {
            middlePartofProof = new List<string>
            {
              ProofUtil.Apply("rule disjI1"),
              ProofUtil.Apply("rule " + blockId + "_def"),
              ProofUtil.Apply("rule " + outEdgesId),
              ProofUtil.Apply("rule cfgDoesntFail"),
              ProofUtil.Apply(ProofUtil.Simp()),
              ProofUtil.Apply("rule cfgSatisfiesPosts"),
              ProofUtil.Apply(ProofUtil.Repeat(ProofUtil.Simp())),
              ProofUtil.Apply("simp add: " + nodeId)
            };
          }
          else if (indicator == BranchIndicator.GuardFails)
          {
            middlePartofProof = new List<string>
            {
              ProofUtil.Apply("rule disjI2"),
              ProofUtil.Apply("rule disjI2"),
              ProofUtil.Apply("rule conjI"),
              ProofUtil.Apply("rule " + blockId + "_def"),
              ProofUtil.Apply("rule conjI"),
              ProofUtil.Apply(ProofUtil.Simp()),
              ProofUtil.Apply("rule conjI"),
              ProofUtil.Apply(" " + NegationRule(entryGuard)),
              ProofUtil.Apply("rule guardHint"),
              ProofUtil.Apply("rule " + outEdgesId),
              ProofUtil.Apply("rule cfgDoesntFail"),
              ProofUtil.Apply(ProofUtil.Simp()),
              ProofUtil.Apply("rule cfgSatisfiesPosts"),
              ProofUtil.Apply(ProofUtil.Repeat(ProofUtil.Simp())),
              ProofUtil.Apply("simp add: " + nodeId)
            };
          } 
          else if (indicator == BranchIndicator.GuardHolds)
          {
            middlePartofProof = new List<string>
            {
              ProofUtil.Apply("rule disjI2"),
              ProofUtil.Apply("rule disjI1"),
              ProofUtil.Apply("rule conjI"),
              ProofUtil.Apply("rule " + blockId + "_def"),
              ProofUtil.Apply("rule conjI"),
              ProofUtil.Apply(ProofUtil.Simp()),
              ProofUtil.Apply("rule guardHint"),
              ProofUtil.Apply("rule " + outEdgesId),
              ProofUtil.Apply("rule cfgDoesntFail"),
              ProofUtil.Apply(ProofUtil.Simp()),
              ProofUtil.Apply("rule cfgSatisfiesPosts"),
              ProofUtil.Apply(ProofUtil.Repeat(ProofUtil.Simp())),
              ProofUtil.Apply("simp add: " + nodeId)
            };
          }
          else
          {
            middlePartofProof = new List<string>
            {
              ProofUtil.Apply("rule disjI1"),
              ProofUtil.Apply("rule " + blockId + "_def"),
              ProofUtil.Apply("rule " + outEdgesId),
              ProofUtil.Apply("rule cfgDoesntFail"),
              ProofUtil.Apply(ProofUtil.Simp()),
              ProofUtil.Apply("rule cfgSatisfiesPosts"),
              ProofUtil.Apply(ProofUtil.Repeat(ProofUtil.Simp())),
              ProofUtil.Apply("simp add: " + nodeId),
            };
          }

          beginningOfProof = new List<string>
          {
            "proof -",
            "show ?thesis",
            ProofUtil.Apply("rule generic_ending_block_global_rel"),
            syntacticRel,
            ProofUtil.Apply("simp add: " + bigblockId + "_def"),
            mappingBigBlockToLocalLemmaDecl.ContainsKey(startingBigBlock) ? ProofUtil.Apply(ProofUtil.Simp()) : "",
            ProofUtil.Apply("rule astTrace"),
            ProofUtil.Apply("simp add: " + bigblockId + "_def"),
            ProofUtil.Apply(ProofUtil.Simp()),
            ProofUtil.Apply(ProofUtil.Simp()),
            startingBigBlock.tc is ReturnCmd ? "" : ProofUtil.Apply("rule " + contId + "_def"),
            ProofUtil.Apply("rule " + nodeId)
          };

          List<string> proofMethods = new List<string>();
          proofMethods.AddRange(beginningOfProof);
          proofMethods.AddRange(middlePartofProof);
          proofMethods.AddRange(finalPartofProof);

          return proofMethods;
        }
        
        private List<string> GenerateLoopHeadProof(
          BigBlock startingBigBlock,
          Block relatedBlock,
          Expr personalGuard,
          ProofGenInfo proofGenInfo)
        {
           List<string> proofMethods = new List<string>();

           BigBlock correspondingBigBlockOrig = proofGenInfo.GetMappingCopyBigblockToOrigBigblock()[startingBigBlock];
           if (proofGenInfo.GetMappingCopyBigblockToOrigBigblockWithTupleValue().Keys.Contains(startingBigBlock))
           {
             correspondingBigBlockOrig = proofGenInfo.GetMappingCopyBigblockToOrigBigblockWithTupleValue()[startingBigBlock].Item2;
           }
           
           //Get the BigBlock that comes after the loop.
           BigBlock afterLoopBigBlockOrig = correspondingBigBlockOrig.successorBigBlock;
           BigBlock afterLoopBigBlockCopy = proofGenInfo.GetMappingOrigBigblockToCopyBigblock()[afterLoopBigBlockOrig];
           
           BigBlock unwrappedAfterLoopBigBlockCopy = null;
           foreach (var tuple in proofGenInfo.GetMappingCopyBigblockToOrigBigblockWithTupleValue())
           {
             if (tuple.Value.Item2 == afterLoopBigBlockOrig)
             {
               unwrappedAfterLoopBigBlockCopy = tuple.Key;
               break;
             }
           }

           //Get the BigBlock that's the first one in the loop body.
           WhileCmd wcmd = (WhileCmd) correspondingBigBlockOrig.ec;
           BigBlock bodyBigBlockOrig = wcmd.Body.BigBlocks.First();
           BigBlock bodyBigBlockCopy = proofGenInfo.GetMappingOrigBigblockToCopyBigblock()[bodyBigBlockOrig];
           
           //Get the successor CFG blocks to the CFG block that's related to the starting BigBlock.
           IEnumerable<Block> successors = afterCfg.GetSuccessorBlocks(relatedBlock);
           if (successors != null && successors.Any())
           {
             Block succ1 = successors.First();
             int succ1UniqueIntLabel = afterCfg.GetUniqueIntLabel(succ1);
             Block succ2 = successors.Last();
             int succ2UniqueIntLabel = afterCfg.GetUniqueIntLabel(succ2);
           
             //Get the names of all of the terms that are to be used in the proof.
             string bigblockId = beforeCfgProgAccess.BigBlockInfo().CmdsQualifiedName(startingBigBlock).First();
             string blockId = afterCfgProgAccess.BlockInfo().getTheoryName() + ".block_" + afterCfg.GetUniqueIntLabel(relatedBlock);
             string nodeId = afterCfgProgAccess.BlockInfo().getTheoryName() + ".node_" + afterCfg.GetUniqueIntLabel(relatedBlock);
             string outEdgesId = afterCfgProgAccess.BlockInfo().getTheoryName() + ".outEdges_" + afterCfg.GetUniqueIntLabel(relatedBlock);
          
             //string bigblockBodyId = beforeCfgProgAccess.BigBlockInfo().CmdsQualifiedName(bodyBigBlockCopy).First();
             string contId = "cont_" + proofGenInfo.GetMappingCopyBigBlockToIndex()[startingBigBlock];
             string bodyBigBlockContId = "cont_" + (proofGenInfo.GetMappingCopyBigBlockToIndex()[bodyBigBlockCopy]);

             #region loop body definitions in simplifier
           
             string unfoldedLoopBodyDefinitions = "apply (simp add: " + contId + "_def ";
             WhileCmd _while = (WhileCmd) correspondingBigBlockOrig.ec;
             foreach (BigBlock bodyBb in _while.Body.BigBlocks)
             {
               BigBlock bodyBbCopy = null;
               if (proofGenInfo.GetMappingOrigBigblockToCopyBigblock().ContainsKey(bodyBb))
               {
                 bodyBbCopy = proofGenInfo.GetMappingOrigBigblockToCopyBigblock()[bodyBb];
               }
               else
               {
                 foreach (var tuple in proofGenInfo.GetMappingCopyBigblockToOrigBigblockWithTupleValue())
                 {
                   if (tuple.Value.Item2 == bodyBb)
                   {
                     bodyBbCopy = tuple.Key;
                     break;
                   }
                 }
               }

               if (bodyBbCopy != null)
               {
                 string currBigBlockId = beforeCfgProgAccess.BigBlockInfo().CmdsQualifiedName(bodyBbCopy).First();
                 string currContId = "cont_" + proofGenInfo.GetMappingCopyBigBlockToIndex()[bodyBbCopy];

                 unfoldedLoopBodyDefinitions =
                   unfoldedLoopBodyDefinitions + currBigBlockId + "_def " + currContId + "_def ";
               }
             }
           
             unfoldedLoopBodyDefinitions += ")";
             #endregion

             string afterLoopBigBlockId = beforeCfgProgAccess.BigBlockInfo().CmdsQualifiedName(afterLoopBigBlockCopy).First();

             string succBlockId1 = afterCfgProgAccess.BlockInfo().getTheoryName() + ".block_" + afterCfg.GetUniqueIntLabel(succ1);
             string succNodeId1 = afterCfgProgAccess.BlockInfo().getTheoryName() + ".node_" + afterCfg.GetUniqueIntLabel(succ1);
             string succOutEdgesId1 = afterCfgProgAccess.BlockInfo().getTheoryName() + ".outEdges_" + afterCfg.GetUniqueIntLabel(succ1);
           
             string afterLoopContId = "cont_" + proofGenInfo.GetMappingCopyBigBlockToIndex()[afterLoopBigBlockCopy];

             string nameLemmaSucc1 = mappingBigBlockToGlobalLemmaDecl[bodyBigBlockCopy].Name;
             string nameLemmaSucc2 = mappingBigBlockToGlobalLemmaDecl[afterLoopBigBlockCopy].Name;

             string unwrappedAfterLoopBigBlockId = "";
             string unwrappedAfterLoopContId = "";
             string nameLemmaSucc3 = "";
             if (unwrappedAfterLoopBigBlockCopy != null)
             {
               unwrappedAfterLoopBigBlockId = beforeCfgProgAccess.BigBlockInfo().CmdsQualifiedName(unwrappedAfterLoopBigBlockCopy).First();
               unwrappedAfterLoopContId = "cont_" + proofGenInfo.GetMappingCopyBigBlockToIndex()[unwrappedAfterLoopBigBlockCopy];
               nameLemmaSucc3 = mappingBigBlockToGlobalLemmaDecl[unwrappedAfterLoopBigBlockCopy].Name;
             }
           
             #region construct proof

             var beginningOfProof = new List<string>
             { 
               "using assms",
               "proof (induction j arbitrary: ns1 rule: less_induct)",
               "case (less j)",
               "then show ?case",
               "proof (cases j)",
               "case 0",
               "then show ?thesis",
               "using valid_configuration_def less.prems(1) is_final.elims(2) " + contId + "_def" + " by fastforce",
               "next",
               "case (Suc j')",
               "show ?thesis",
               ProofUtil.Apply("rule block_global_rel_loop_head "),
               ProofUtil.Apply("rule Rel_Invs[of " + bigblockId + " _ _ _ " + blockId + "]"),
               ProofUtil.Apply("simp add:" + bigblockId + "_def " + blockId + "_def"),
               ProofUtil.Apply("rule less(2)"),
               ProofUtil.Apply("rule less(3), simp"),
               ProofUtil.Apply("rule less(4), simp"),
               ProofUtil.Apply(ProofUtil.Simp()),
               ProofUtil.Apply("simp add:" + bigblockId + "_def"),
               "apply simp                 ",
               ProofUtil.Apply("rule block_local_rel_loop_head"),
               ProofUtil.Apply("rule Rel_Invs[of " + bigblockId + "]"),
               ProofUtil.Apply(ProofUtil.Repeat("simp add:" + bigblockId + "_def")),
               ProofUtil.Apply(ProofUtil.Repeat("simp add:" + blockId + "_def " + nodeId)),
               ProofUtil.Apply("rule " + contId + "_def"),
               ProofUtil.Apply("erule disjE"),
               
               personalGuard == null ? ProofUtil.Apply(ProofUtil.Repeat(ProofUtil.Simp())) : null,
               personalGuard == null ? "apply (erule disjE)" : null,
               //TODO: get rid of this
               personalGuard == null ? "defer" : null,

               ProofUtil.Apply(ProofUtil.Repeat("erule allE[where x = " + succ2UniqueIntLabel + "]")),
               ProofUtil.Apply(ProofUtil.Repeat("simp add:" + outEdgesId)),
               ProofUtil.Apply("simp add:member_rec(1)"),
               personalGuard != null ? ProofUtil.Apply("erule conjE") : null,
               ProofUtil.Apply("rule " + nameLemmaSucc1 + ""),
               unfoldedLoopBodyDefinitions,
               ProofUtil.Apply(ProofUtil.Repeat("blast")),
               ProofUtil.Apply("rule loop_IH_prove"),
               ProofUtil.Apply("rule less.IH"),
               ProofUtil.Apply("erule strictly_smaller_helper2"),
               ProofUtil.Apply(ProofUtil.Simp()),
               "unfolding " + contId + "_def " + bodyBigBlockContId + "_def",
               ProofUtil.Apply(ProofUtil.Simp()),
               ProofUtil.Apply("blast"),
               ProofUtil.Apply("blast"),
               
               proofGenInfo.GetMappingBigBlockToLoopBigBlock().ContainsKey(correspondingBigBlockOrig) &&
               personalGuard == null
                 ? ProofUtil.Apply("rule guardHint")
                 : null, 
             };

             var insideOfLoopAddition1 = new List<string>
             {
               ProofUtil.Apply("rule loop_IH_prove"),
               ProofUtil.Apply("rule loop_IH_apply"),
               
               proofGenInfo.GetMappingBigBlockToLoopBigBlock().ContainsKey(correspondingBigBlockOrig) &&
               personalGuard == null 
                 ? ProofUtil.Apply("rule less(6)")
                 : ProofUtil.Apply("rule less(5)"),
               
               ProofUtil.Apply("rule strictly_smaller_helper3"),
               ProofUtil.Apply(ProofUtil.Repeat(ProofUtil.Simp())),
             };
           
             var insideOfLoopAddition2 = new List<string>
             {
               ProofUtil.Apply("rule loop_IH_prove"),
               ProofUtil.Apply("rule loop_IH_apply"),
               
               proofGenInfo.GetMappingBigBlockToLoopBigBlock().ContainsKey(correspondingBigBlockOrig) &&
               personalGuard == null 
                ? ProofUtil.Apply("rule less(6)")
                : ProofUtil.Apply("rule less(5)"),
               
               ProofUtil.Apply("rule strictly_smaller_helper4"),
               ProofUtil.Apply(ProofUtil.Repeat(ProofUtil.Simp())),
             };

             var whileTrueEndingAfterSkippingEndBlock = new List<string>
             {
               personalGuard == null && !proofGenInfo.GetMappingBigBlockToLoopBigBlock()
                 .ContainsKey(correspondingBigBlockOrig)
                 ? ProofUtil.Apply("rule guardHint")
                 : null,
               ProofUtil.Apply(ProofUtil.Repeat("erule allE[where x = " + succ1UniqueIntLabel + "]")),
               ProofUtil.Apply(ProofUtil.Repeat("simp add:" + outEdgesId)),
               ProofUtil.Apply("simp add:member_rec(1)"),
               personalGuard != null ? ProofUtil.Apply("erule conjE") : null,
               ProofUtil.Apply("rule ending_after_skipping_endblock2"),

               //TODO: repeat is possibly redundant here!
               ProofUtil.Apply(ProofUtil.Repeat(ProofUtil.Simp())),
               ProofUtil.Apply("blast"),
               personalGuard != null ? ProofUtil.Apply("blast") : ProofUtil.Apply(ProofUtil.Repeat("blast")),
               personalGuard != null ? ProofUtil.Apply(ProofUtil.Simp()) : null,

               personalGuard != null && !personalGuard.Equals(Expr.True) ? ProofUtil.Apply(ProofUtil.Simp()) : null,
               personalGuard != null && !personalGuard.Equals(Expr.True)
                 ? ProofUtil.Apply("rule " + nameLemmaSucc2 + "")
                 : null,

               //TODO: repeat is redundant here!
               personalGuard != null && !personalGuard.Equals(Expr.True) ? ProofUtil.Apply("blast") : null,

               //afterLoopBigBlockOrig.successorBigBlock != null ? "apply blast" : null,
               personalGuard == null ? ProofUtil.Apply("rule " + nameLemmaSucc2) : null,
               personalGuard == null ? ProofUtil.Apply(ProofUtil.Simp()) : null,
               
               ProofUtil.Apply("blast")
             };
             
             var endingAfterSkippingEndblock = new List<string>
             {
               personalGuard == null && !proofGenInfo.GetMappingBigBlockToLoopBigBlock().ContainsKey(correspondingBigBlockOrig) ? ProofUtil.Apply("rule guardHint") : null,
               ProofUtil.Apply(ProofUtil.Repeat("erule allE[where x = " + succ1UniqueIntLabel + "]")),
               ProofUtil.Apply(ProofUtil.Repeat("simp add:" + outEdgesId)),
               ProofUtil.Apply("simp add:member_rec(1)"),
               personalGuard != null ? ProofUtil.Apply("erule conjE") : null,
               ProofUtil.Apply("rule ending_after_skipping_endblock2"),
             
               //TODO: repeat is possibly redundant here!
               ProofUtil.Apply(ProofUtil.Repeat(ProofUtil.Simp())),
               ProofUtil.Apply("blast"),
               personalGuard != null ? ProofUtil.Apply("blast") : ProofUtil.Apply(ProofUtil.Repeat("blast")),
               personalGuard != null ? ProofUtil.Apply(ProofUtil.Simp()) : null,

               personalGuard != null && !personalGuard.Equals(Expr.True) ? ProofUtil.Apply(ProofUtil.Simp()) : null,
               personalGuard != null && !personalGuard.Equals(Expr.True) ? ProofUtil.Apply("rule " + nameLemmaSucc2 + "") : null,
             
               //TODO: repeat is redundant here!
               personalGuard != null && !personalGuard.Equals(Expr.True) ? ProofUtil.Apply("blast") : null,
             
               //afterLoopBigBlockOrig.successorBigBlock != null ? "apply blast" : null,
               personalGuard == null ? ProofUtil.Apply("rule " + nameLemmaSucc2) : null,
               personalGuard == null ? ProofUtil.Apply(ProofUtil.Simp()) : null,
               
               proofGenInfo.GetloopEndingBlocks().Contains(afterLoopBigBlockOrig) ? ProofUtil.Apply(ProofUtil.Repeat("blast")) : null,
               
               !proofGenInfo.GetloopEndingBlocks().Contains(afterLoopBigBlockOrig)
                 ? (personalGuard != null
                   ? ProofUtil.Apply("rule correctness_propagates_through_assumption")
                   : ProofUtil.Apply("rule correctness_propagates_through_empty"))
                 : null,
               !proofGenInfo.GetloopEndingBlocks().Contains(afterLoopBigBlockOrig) ? "apply blast" : null,
               !proofGenInfo.GetloopEndingBlocks().Contains(afterLoopBigBlockOrig) ? ProofUtil.Apply("simp add: " + succNodeId1 + "") : null,
               !proofGenInfo.GetloopEndingBlocks().Contains(afterLoopBigBlockOrig) ? ProofUtil.Apply("simp add: " + succBlockId1 + "_def") : null,
               !proofGenInfo.GetloopEndingBlocks().Contains(afterLoopBigBlockOrig)
                 ? (personalGuard != null
                   ? ProofUtil.Apply(NegationRule(personalGuard))
                   : null)
                 : null, 
               !proofGenInfo.GetloopEndingBlocks().Contains(afterLoopBigBlockOrig) ? ProofUtil.Apply(ProofUtil.Simp()) : null,
               !proofGenInfo.GetloopEndingBlocks().Contains(afterLoopBigBlockOrig) ? ProofUtil.Apply("simp add: " + succOutEdgesId1 + "") : null,
               !proofGenInfo.GetloopEndingBlocks().Contains(afterLoopBigBlockOrig) ? ProofUtil.Apply(ProofUtil.Repeat("simp add: member_rec")) : null,
               !proofGenInfo.GetloopEndingBlocks().Contains(afterLoopBigBlockOrig)
                 ? (personalGuard != null
                   ? ProofUtil.Apply("rule correctness_propagates_through_assumption3")
                   : ProofUtil.Apply("rule correctness_propagates_through_empty2"))
                 : null,
               !proofGenInfo.GetloopEndingBlocks().Contains(afterLoopBigBlockOrig) ? "apply blast" : null,
               !proofGenInfo.GetloopEndingBlocks().Contains(afterLoopBigBlockOrig) ? ProofUtil.Apply("simp add: " + succNodeId1 + "") : null,
               !proofGenInfo.GetloopEndingBlocks().Contains(afterLoopBigBlockOrig) ? ProofUtil.Apply("simp add: " + succBlockId1 + "_def") : null,
               !proofGenInfo.GetloopEndingBlocks().Contains(afterLoopBigBlockOrig)
                 ? (personalGuard != null
                   ? ProofUtil.Apply(NegationRule(personalGuard))
                   : null)
                 : null, 
               !proofGenInfo.GetloopEndingBlocks().Contains(afterLoopBigBlockOrig) ? ProofUtil.Apply(ProofUtil.Simp()) : null,
               !proofGenInfo.GetloopEndingBlocks().Contains(afterLoopBigBlockOrig) ? ProofUtil.Apply("simp add: " + succOutEdgesId1 + "") : null,
               !proofGenInfo.GetloopEndingBlocks().Contains(afterLoopBigBlockOrig) ? ProofUtil.Apply(ProofUtil.Repeat("simp add: member_rec")) : null
             };

             var endingAfterSkippingEndBlockAndUnwrapping = new List<string>
             {
               ProofUtil.Apply(ProofUtil.Repeat("erule allE[where x = " + succ1UniqueIntLabel + "]")),
               ProofUtil.Apply(ProofUtil.Repeat("simp add:" + outEdgesId)),
               ProofUtil.Apply("simp add:member_rec(1)"),
               ProofUtil.Apply("erule conjE"),

               ProofUtil.Apply("rule ending_after_skipping_endblock_and_unwrapping"),
               "apply assumption",
               ProofUtil.Apply("simp add: " + afterLoopBigBlockId + "_def"),
               ProofUtil.Apply(ProofUtil.Simp()),
               "apply assumption",
               "apply blast",
               ProofUtil.Apply(ProofUtil.Simp()),
               ProofUtil.Apply("simp add:" + succNodeId1 + ""),
               ProofUtil.Apply("simp add:" + succBlockId1 + "_def"),
               ProofUtil.Apply(NegationRule(personalGuard)),
               ProofUtil.Apply("simp add:" + succOutEdgesId1),
               ProofUtil.Apply("simp add: member_rec"),
               ProofUtil.Apply("simp add:" + succNodeId1),
               ProofUtil.Apply("simp add:" + succOutEdgesId1),
               ProofUtil.Apply("simp add: member_rec"),
               ProofUtil.Apply("rule " + nameLemmaSucc3),
               ProofUtil.Apply("simp add: " + unwrappedAfterLoopBigBlockId + "_def " + afterLoopContId + "_def " + unwrappedAfterLoopContId + "_def"),
               ProofUtil.Apply("rule correctness_propagates_through_assumption"),
               "apply blast",
               ProofUtil.Apply("simp add:" + succNodeId1 + ""),
               ProofUtil.Apply(ProofUtil.Repeat(ProofUtil.Simp())),
               ProofUtil.Apply("simp add:" + succOutEdgesId1 + ""),
               ProofUtil.Apply("simp add: member_rec"),
               "apply blast",
               ProofUtil.Apply("rule correctness_propagates_through_assumption3"),
               ProofUtil.Apply(ProofUtil.Repeat("simp add:" + succNodeId1)),
               ProofUtil.Apply("simp add:" + succOutEdgesId1),
               ProofUtil.Apply(ProofUtil.Repeat("simp add: member_rec"))
             };
             
             proofMethods.AddRange(beginningOfProof);
           
             if (proofGenInfo.GetMappingBigBlockToLoopBigBlock().ContainsKey(correspondingBigBlockOrig))
             {
               proofMethods.AddRange(insideOfLoopAddition1);
             }

             //TODO: do the second check if BlockCoalescing is activated, otherwise keep as is
             if (personalGuard != null && personalGuard.Equals(Expr.True))
             {
               proofMethods.AddRange(whileTrueEndingAfterSkippingEndBlock); 
             }
             else
             {
               proofMethods.AddRange(endingAfterSkippingEndblock);
             }
             // if (afterLoopBigBlockOrig.ec is WhileCmd && !afterLoopBigBlockCopy.simpleCmds.Any())
             // {
             //   proofMethods.AddRange(endingAfterSkippingEndBlockAndUnwrapping);
             // }
             // else
             // {
             //   proofMethods.AddRange(endingAfterSkippingEndblock);
             // }

             if (proofGenInfo.GetMappingBigBlockToLoopBigBlock().ContainsKey(correspondingBigBlockOrig))
             {
               proofMethods.AddRange(insideOfLoopAddition2);
             }
           
             proofMethods.AddRange(
               new List<string>
               {
                 "done",
                 "qed",
                 "qed"
               });
           
             #endregion
             
           }
           return proofMethods;
        }
        
        private List<string> GenerateProofGeneric(
          BigBlock startingBigBlock,
          Block relatedBlock,
          Expr entryGuard,
          BranchIndicator indicator,
          ProofGenInfo proofGenInfo)
        {
          string bigblockId = beforeCfgProgAccess.BigBlockInfo().CmdsQualifiedName(startingBigBlock).First();
          string blockId = afterCfgProgAccess.BlockInfo().getTheoryName() + ".block_" + afterCfg.GetUniqueIntLabel(relatedBlock);
          string nodeId = afterCfgProgAccess.BlockInfo().getTheoryName() + ".node_" + afterCfg.GetUniqueIntLabel(relatedBlock);
          string outEdgesId = afterCfgProgAccess.BlockInfo().getTheoryName() + ".outEdges_" + afterCfg.GetUniqueIntLabel(relatedBlock);
          string contId = "cont_" + proofGenInfo.GetMappingCopyBigBlockToIndex()[startingBigBlock];
            
          BigBlock correspondingBigBlockOrig = proofGenInfo.GetMappingCopyBigblockToOrigBigblock()[startingBigBlock];
          BigBlock successorBigBlockOrig = correspondingBigBlockOrig.successorBigBlock;
          BigBlock successorBigBlockCopy = proofGenInfo.GetMappingOrigBigblockToCopyBigblock()[successorBigBlockOrig];

          foreach (var kvPair in proofGenInfo.GetMappingCopyBigblockToOrigBigblockWithTupleValue())
          {
            if (kvPair.Value.Item2 == successorBigBlockOrig)
            {
              successorBigBlockCopy = kvPair.Key;
              break;
            }
          }

          int succUniqueLoopLabel = -1;
          if (proofGenInfo.GetMappingBigBlockToLoopBigBlock().ContainsKey(correspondingBigBlockOrig))
          {
            BigBlock loop = proofGenInfo.GetMappingBigBlockToLoopBigBlock()[correspondingBigBlockOrig];
            BigBlock loopCopy = proofGenInfo.GetMappingOrigBigblockToCopyBigblock()[loop];
            
            IDictionary<Block, Block> origBlockBeforeDag = beforeDagOrigBlock.InverseDict();
            
            Block enclosingLoopCfgBlock = proofGenInfo.GetMappingOrigBigBlockToOrigBlock()[loop];
            Block enclosingLoopCfgBlockCopy = origBlockBeforeDag[enclosingLoopCfgBlock];

            if (true /* enclosingLoopCfgBlockCopy.cmds.Any() */)
            {
              Block successorCfgBlock = afterCfg.GetSuccessorBlocks(enclosingLoopCfgBlockCopy).First();
              //Block successorCfgBlockCopy = origBlockBeforeDag[successorCfgBlock];
              
              succUniqueLoopLabel = afterCfg.GetUniqueIntLabel(successorCfgBlock);
            }
            else
            {
              succUniqueLoopLabel = afterCfg.GetUniqueIntLabel(enclosingLoopCfgBlockCopy); 
            }
            
            //succUniqueLoopLabel = proofGenInfo.getMappingCopyBigBlockToIndex()[loopCopy];
            //succUniqueLoopLabel += 1;
          }
          
          var proofMethods = new List<string>();
          IEnumerable<Block> successors = afterCfg.GetSuccessorBlocks(relatedBlock);
          if (successors != null && successors.Any())
          {
            Block succ1 = successors.First();
            int succUniqueIntLabel = afterCfg.GetUniqueIntLabel(succ1);

            string nameLemmaLocal = "prelimNameTest";
            if (mappingBigBlockToLocalLemmaDecl.ContainsKey(startingBigBlock))
            {
              nameLemmaLocal = mappingBigBlockToLocalLemmaDecl[startingBigBlock].Name;
            }
          
            string nameLemmaSucc = "nameLemmaSuccTest";
            if (!proofGenInfo.GetMappingBigBlockToLoopBigBlock().ContainsKey(correspondingBigBlockOrig) || 
                correspondingBigBlockOrig.successorBigBlock != proofGenInfo.GetMappingBigBlockToLoopBigBlock()[correspondingBigBlockOrig])
            {
              nameLemmaSucc = mappingBigBlockToGlobalLemmaDecl[successorBigBlockCopy].Name; 
            }

            var beginningOfProof = new List<string>
            {
              "proof -",
              "show ?thesis ",
              ProofUtil.Apply("rule block_global_rel_generic"),
              startingBigBlock.simpleCmds.Any() ? ProofUtil.Apply("rule Rel_Main_test[of " + bigblockId + "]") : ProofUtil.Apply("rule Rel_Invs[of " + bigblockId + "]") ,
              ProofUtil.Apply("simp add: " + bigblockId + "_def"),
              startingBigBlock.simpleCmds.Any() ? ProofUtil.Apply(ProofUtil.Simp()) : null,
              ProofUtil.Apply("rule astTrace"),
              ProofUtil.Apply("simp add: " + bigblockId + "_def"),
              ProofUtil.Apply("rule " + nodeId + "")
            };

            var middlePartOfProof = new List<string>();
            if (indicator == 0 || entryGuard == null)
            {
              middlePartOfProof = new List<string>
              {
                ProofUtil.Apply("rule disjI1"),
                ProofUtil.Apply("rule " + blockId + "_def"),
                // indicator == BranchIndicator.GuardHolds || indicator == BranchIndicator.GuardFails ? ProofUtil.Apply("rule conjI") : null,
                // indicator == BranchIndicator.GuardHolds || indicator == BranchIndicator.GuardFails ? ProofUtil.Apply(ProofUtil.Simp()) : null,
                ProofUtil.Apply("rule cfgDoesntFail"),
                ProofUtil.Apply(ProofUtil.Repeat(ProofUtil.Simp())),
                ProofUtil.Apply("rule cfgSatisfiesPosts, blast"),
                ProofUtil.Apply(ProofUtil.Repeat(ProofUtil.Simp())),
                ProofUtil.Apply("rule " + contId + "_def"),
                ProofUtil.Apply("simp add: " + nodeId + ""),
                // !startingBigBlock.simpleCmds.Any() ? ProofUtil.Apply(ProofUtil.Simp()) : null,
                startingBigBlock.simpleCmds.Any() ? ProofUtil.Apply("rule " + nameLemmaLocal + "") : null,
                startingBigBlock.simpleCmds.Any() ? "apply assumption" : null,
                startingBigBlock.simpleCmds.Any() ? ProofUtil.Apply(ProofUtil.Simp()) : null,
              };
            }
            else if (indicator == BranchIndicator.GuardFails)
            {
              middlePartOfProof = new List<string>
              {
                ProofUtil.Apply("rule disjI2"),
                ProofUtil.Apply("rule disjI2"),
                ProofUtil.Apply("rule conjI"),
                ProofUtil.Apply("rule " + blockId + "_def"),
                ProofUtil.Apply("rule conjI"),
                ProofUtil.Apply(ProofUtil.Simp()),
                ProofUtil.Apply("rule conjI"),
                ProofUtil.Apply("" + NegationRule(entryGuard) + ""),
                ProofUtil.Apply("rule guardHint"),
                ProofUtil.Apply("rule cfgDoesntFail"),
                ProofUtil.Apply(ProofUtil.Repeat(ProofUtil.Simp())),
                ProofUtil.Apply("rule cfgSatisfiesPosts, blast"),
                ProofUtil.Apply(ProofUtil.Repeat(ProofUtil.Simp())),
                ProofUtil.Apply("rule " + contId + "_def"),
                ProofUtil.Apply("simp add: " + nodeId + ""),
                //!startingBigBlock.simpleCmds.Any() ? ProofUtil.Apply(ProofUtil.Simp()) : null,
                startingBigBlock.simpleCmds.Any() ? ProofUtil.Apply("rule " + nameLemmaLocal + "") : null,
                startingBigBlock.simpleCmds.Any() ? "apply assumption" : null,
                startingBigBlock.simpleCmds.Any() ? ProofUtil.Apply(ProofUtil.Simp()) : null,
                startingBigBlock.simpleCmds.Any() ? ProofUtil.Apply("rule guardHint") : null,
              };
            }
            //TODO: this check isn't correct! Why?
            else if (indicator == BranchIndicator.GuardHolds || proofGenInfo.GetMappingBigBlockToLoopBigBlock().ContainsKey(correspondingBigBlockOrig))
            {
              middlePartOfProof = new List<string>
              {
                ProofUtil.Apply("rule disjI2"),
                ProofUtil.Apply("rule disjI1"),
                ProofUtil.Apply("rule conjI"),
                ProofUtil.Apply("rule " + blockId + "_def"),
                ProofUtil.Apply("rule conjI"),
                ProofUtil.Apply(ProofUtil.Simp()),
                ProofUtil.Apply("rule guardHint"),
                ProofUtil.Apply("rule cfgDoesntFail"),
                ProofUtil.Apply(ProofUtil.Repeat(ProofUtil.Simp())),
                ProofUtil.Apply("rule cfgSatisfiesPosts, blast"),
                ProofUtil.Apply(ProofUtil.Repeat(ProofUtil.Simp())),
                ProofUtil.Apply("rule " + contId + "_def"),
                ProofUtil.Apply("simp add: " + nodeId + ""),
                //!startingBigBlock.simpleCmds.Any() ? ProofUtil.Apply(ProofUtil.Simp()) : null,
                startingBigBlock.simpleCmds.Any() ? ProofUtil.Apply("rule " + nameLemmaLocal + "") : null,
                startingBigBlock.simpleCmds.Any() ? "apply assumption" : null,
                startingBigBlock.simpleCmds.Any() ? ProofUtil.Apply(ProofUtil.Simp()) : null,
                startingBigBlock.simpleCmds.Any() && indicator == BranchIndicator.GuardHolds ? ProofUtil.Apply("rule guardHint") : null,
              };
            }

            var proofEnd = new List<string>();
            if (proofGenInfo.GetMappingBigBlockToLoopBigBlock().ContainsKey(correspondingBigBlockOrig) &&
                correspondingBigBlockOrig.successorBigBlock.ec is WhileCmd)
            {
              proofEnd = new List<string>
              {
                ProofUtil.Apply(ProofUtil.Repeat("erule allE[where x=" + succUniqueLoopLabel + "]")),
                ProofUtil.Apply("simp add: " + outEdgesId + ""),
                ProofUtil.Apply("simp add: member_rec(1)"),
                ProofUtil.Apply("rule loop_IH_apply"),
                ProofUtil.Apply("rule inductionHypothesis"), 
                ProofUtil.Apply(ProofUtil.Repeat(ProofUtil.Simp()))
              };
            }
            else
            {
              proofEnd = new List<string>
              {
                ProofUtil.Apply(ProofUtil.Repeat("erule allE[where x = " + succUniqueIntLabel + "]")),
                ProofUtil.Apply(ProofUtil.Repeat("simp add: " + outEdgesId)),
                ProofUtil.Apply("simp add: member_rec(1)"),
                ProofUtil.Apply("rule " + nameLemmaSucc + ""),
                !proofGenInfo.GetMappingBigBlockToLoopBigBlock().ContainsKey(correspondingBigBlockOrig) ? ProofUtil.Apply(ProofUtil.Simp()) : null,
                "apply blast+",
                proofGenInfo.GetMappingBigBlockToLoopBigBlock().ContainsKey(correspondingBigBlockOrig) ? ProofUtil.Apply("rule loop_IH_prove") : null,
                proofGenInfo.GetMappingBigBlockToLoopBigBlock().ContainsKey(correspondingBigBlockOrig) ? ProofUtil.Apply("rule loop_IH_apply") : null,
                proofGenInfo.GetMappingBigBlockToLoopBigBlock().ContainsKey(correspondingBigBlockOrig) ? ProofUtil.Apply("rule inductionHypothesis") : null,
                proofGenInfo.GetMappingBigBlockToLoopBigBlock().ContainsKey(correspondingBigBlockOrig) ? ProofUtil.Apply("rule less_trans_inv") : null,
                proofGenInfo.GetMappingBigBlockToLoopBigBlock().ContainsKey(correspondingBigBlockOrig) ? "apply blast+" : null,
              };
            }

            //TODO: name the assumptions
            proofMethods.AddRange(beginningOfProof);
            proofMethods.AddRange(middlePartOfProof);
            proofMethods.AddRange(proofEnd);
            proofMethods.AddRange(
              new List<string>
              {
                "done",
                "qed"
              });
          }
          return proofMethods;
        }
        

        private List<string> GenerateEndingAfterUnwrappingProof( 
          BigBlock startingBigBlock,
          Block relatedBlock,
          Expr entryGuard,
          BranchIndicator indicator,
          ProofGenInfo proofGenInfo)
        {
          BigBlock correspondingOrigBigBlock = proofGenInfo.GetMappingCopyBigblockToOrigBigblock()[startingBigBlock];
          List<string> loopExtension = new List<string>();
          if (proofGenInfo.GetMappingBigBlockToLoopBigBlock().ContainsKey(correspondingOrigBigBlock))
          {
            loopExtension = new List<string>
            {
              ProofUtil.Apply("rule loop_IH_prove"),
              ProofUtil.Apply("rule loop_IH_apply"),
              ProofUtil.Apply("rule inductionHypothesis"),
              ProofUtil.Apply("rule strictly_smaller_helper2"),
              ProofUtil.Apply(ProofUtil.Repeat(ProofUtil.Simp())),
            };
          }
          
          string bigblockId = beforeCfgProgAccess.BigBlockInfo().CmdsQualifiedName(startingBigBlock).First();
          string blockId = afterCfgProgAccess.BlockInfo().getTheoryName() + ".block_" + afterCfg.GetUniqueIntLabel(relatedBlock);
          string nodeId = afterCfgProgAccess.BlockInfo().getTheoryName() + ".node_" + afterCfg.GetUniqueIntLabel(relatedBlock);
          string outEdgesId = afterCfgProgAccess.BlockInfo().getTheoryName() + ".outEdges_" + afterCfg.GetUniqueIntLabel(relatedBlock);
          
          BigBlock correspondingOrig = proofGenInfo.GetMappingCopyBigblockToOrigBigblock()[startingBigBlock];
          BigBlock unwrappedBigBlockCopy = null;
          foreach (var tuple in proofGenInfo.GetMappingCopyBigblockToOrigBigblockWithTupleValue())
          {
            if (tuple.Value.Item2 == correspondingOrig)
            {
              unwrappedBigBlockCopy = tuple.Key;
              break;
            }
          }
          
          string succBigBlockId = beforeCfgProgAccess.BigBlockInfo().CmdsQualifiedName(unwrappedBigBlockCopy).First();

          string contId = "cont_" + proofGenInfo.GetMappingCopyBigBlockToIndex()[startingBigBlock];
          string succContId = "cont_" + proofGenInfo.GetMappingCopyBigBlockToIndex()[unwrappedBigBlockCopy];

          //string nameLemmaLocal = mappingBigBlockToLocalLemmaDecl[startingBigBlock].Name;
          string nameLemmaSuccGlobal = mappingBigBlockToGlobalLemmaDecl[unwrappedBigBlockCopy].Name;

          string correctnessPropagates = null;
          string correctnessPropagatesPosts = null;
          if (entryGuard == null)
          { correctnessPropagates =  ProofUtil.Apply("rule correctness_propagates_through_empty"); 
              correctnessPropagatesPosts = ProofUtil.Apply("rule correctness_propagates_through_empty2"); }
          else if (indicator == BranchIndicator.GuardFails)
          { correctnessPropagates = ProofUtil.Apply("rule correctness_propagates_through_assumption");
            correctnessPropagatesPosts = ProofUtil.Apply("rule correctness_propagates_through_assumption3"); } 
          else if (indicator == BranchIndicator.GuardHolds)
          { correctnessPropagates =  ProofUtil.Apply("rule correctness_propagates_through_assumption2"); 
            correctnessPropagatesPosts = ProofUtil.Apply("rule correctness_propagates_through_assumption4"); }
          else if (indicator == BranchIndicator.NoGuard)
          { correctnessPropagates =  ProofUtil.Apply("rule correctness_propagates_through_empty"); 
            correctnessPropagatesPosts = ProofUtil.Apply("rule correctness_propagates_through_empty2"); }

          string rule = "apply( " + NegationRule(entryGuard) + ")";
          if (indicator == BranchIndicator.GuardHolds || indicator == BranchIndicator.NoGuard || entryGuard == null)
          {
            rule = "";
          }

          List<string> proofMethods = new List<string>
          {
            ProofUtil.Apply("rule ending_after_unwrapping"),
            ProofUtil.Apply("rule astTrace"),
            ProofUtil.Apply("simp add: " + bigblockId + "_def"),
            ProofUtil.Apply("rule cfgDoesntFail, simp"),
            ProofUtil.Apply("rule cfgSatisfiesPosts, blast"),
            ProofUtil.Apply(ProofUtil.Simp()),
            ProofUtil.Apply("rule " + nameLemmaSuccGlobal + ""),
            ProofUtil.Apply("simp add: " + succBigBlockId + "_def " + contId + "_def " + succContId + "_def"),
            correctnessPropagates,
            "using assms(2)",
            "apply blast",
            ProofUtil.Apply("simp add: " + nodeId + ""),
            ProofUtil.Apply("simp add: " + blockId + "_def"),
            indicator != BranchIndicator.NoGuard ? rule : null,
            (indicator != BranchIndicator.NoGuard && entryGuard != null) ? ProofUtil.Apply("rule guardHint") : null,
            ProofUtil.Apply("simp add: " + outEdgesId + ""),
            ProofUtil.Apply("simp add: member_rec"),
            ProofUtil.Apply(ProofUtil.Simp()),
            correctnessPropagatesPosts,
            "using assms(3)",
            "apply blast",
            ProofUtil.Apply("simp add: " + nodeId + ""),
            ProofUtil.Apply("simp add: " + blockId + "_def"),
            indicator != BranchIndicator.NoGuard ? rule : null,
            (indicator != BranchIndicator.NoGuard && entryGuard != null) ? ProofUtil.Apply("rule guardHint") : null,
            ProofUtil.Apply("simp add: " + outEdgesId + ""),
            ProofUtil.Apply("simp add: member_rec"),
            ProofUtil.Apply(ProofUtil.Repeat(ProofUtil.Simp()))
          };
          
          proofMethods.AddRange(loopExtension);
          proofMethods.Add("done");

          return proofMethods;
        }

        private List<string> GenerateWhileSuccessorProof(
          BigBlock startingBigBlock,
          Block relatedBlock,
          Expr entryGuard,
          Expr personalGuard,
          BranchIndicator indicator,
          ProofGenInfo proofGenInfo) 
        { 
           string bigblockId = beforeCfgProgAccess.BigBlockInfo().CmdsQualifiedName(startingBigBlock).First();
           string blockId = afterCfgProgAccess.BlockInfo().getTheoryName() + ".block_" + afterCfg.GetUniqueIntLabel(relatedBlock);
           string nodeId = afterCfgProgAccess.BlockInfo().getTheoryName() + ".node_" + afterCfg.GetUniqueIntLabel(relatedBlock);
           string outEdgesId = afterCfgProgAccess.BlockInfo().getTheoryName() + ".outEdges_" + afterCfg.GetUniqueIntLabel(relatedBlock);

           BigBlock correspondingBigBlockOrig = proofGenInfo.GetMappingCopyBigblockToOrigBigblock()[startingBigBlock];
           BigBlock successorBigBlockCopy = null;
           foreach (var tuple in proofGenInfo.GetMappingCopyBigblockToOrigBigblockWithTupleValue())
           {
             if (correspondingBigBlockOrig == tuple.Value.Item2)
             {
               successorBigBlockCopy = tuple.Key;
               break;
             }
           }

           string succBigBlockId = beforeCfgProgAccess.BigBlockInfo().CmdsQualifiedName(successorBigBlockCopy).First();

           WhileCmd wcmd = (WhileCmd) correspondingBigBlockOrig.ec;
           BigBlock bodyBigBlockOrig = wcmd.Body.BigBlocks.First();
           BigBlock bodyBigBlockCopy = proofGenInfo.GetMappingOrigBigblockToCopyBigblock()[bodyBigBlockOrig];

           var proofMethods = new List<string>();
           IEnumerable<Block> successors = afterCfg.GetSuccessorBlocks(relatedBlock);
           if (successors != null && successors.Any())
           {
             Block succ = successors.First();
             int succUniqueIntLabel = afterCfg.GetUniqueIntLabel(succ);
           
             string contId = "cont_" + proofGenInfo.GetMappingCopyBigBlockToIndex()[startingBigBlock];
             string successorContId = "cont_" + (proofGenInfo.GetMappingCopyBigBlockToIndex()[successorBigBlockCopy]);

             string nameLemmaSucc = mappingBigBlockToGlobalLemmaDecl[successorBigBlockCopy].Name;
             string nameLemmaLocal = null;
          
             if (mappingBigBlockToLocalLemmaDecl.ContainsKey(startingBigBlock))
             {
               nameLemmaLocal = mappingBigBlockToLocalLemmaDecl[startingBigBlock].Name; 
             }
             
             proofMethods = new List<string>
             {
               "proof -",
               "show ?thesis",
               ProofUtil.Apply("rule block_global_rel_while_successor"),
               ProofUtil.Apply("rule astTrace"),
               indicator == BranchIndicator.GuardHolds || indicator == BranchIndicator.GuardFails ? 
                 ProofUtil.Apply("rule Rel_Main_test[of " + bigblockId + "]") : ProofUtil.Apply("rule Rel_Main_test[of " + bigblockId + " _ " + blockId + "]"),
               ProofUtil.Apply("simp add: " + bigblockId + "_def " + blockId + "_def"),
               ProofUtil.Apply("simp add: " + bigblockId + "_def " + blockId + "_def"),
               ProofUtil.Apply("simp add: " + bigblockId + "_def " + blockId + "_def"),
               ProofUtil.Apply("simp add: " + blockId + "_def"),
               ProofUtil.Apply("rule " + nodeId + ""),
             
               entryGuard == null ? ProofUtil.Apply("rule disjI1") : null,
              
               entryGuard != null ? (indicator == BranchIndicator.NoGuard ? ProofUtil.Apply("rule disjI1") : ProofUtil.Apply("rule disjI2")) : null,
               entryGuard != null && indicator == BranchIndicator.GuardHolds ? ProofUtil.Apply("rule disjI1") : null,
               entryGuard != null && indicator == BranchIndicator.GuardFails ? ProofUtil.Apply("rule disjI2") : null,
               
               ProofUtil.Apply("simp add: " + blockId + "_def"),
               entryGuard != null && (indicator == BranchIndicator.GuardHolds || indicator == BranchIndicator.GuardFails) ? ProofUtil.Apply("rule conjI") : null,
               entryGuard != null && (indicator == BranchIndicator.GuardHolds || indicator == BranchIndicator.GuardFails) ? ProofUtil.Apply(ProofUtil.Simp()) : null,
               entryGuard != null && (indicator == BranchIndicator.GuardHolds || indicator == BranchIndicator.GuardFails) ? ProofUtil.Apply("rule conjI") : null,
               entryGuard != null && (indicator == BranchIndicator.GuardHolds || indicator == BranchIndicator.GuardFails) ? ProofUtil.Apply(ProofUtil.Simp()) : null,
               entryGuard != null && (indicator == BranchIndicator.GuardFails) ? ProofUtil.Apply("rule conjI") : null,
               entryGuard != null && (indicator == BranchIndicator.GuardFails) ? ProofUtil.Apply("" + NegationRule(entryGuard) + "") : null,
               entryGuard != null && (indicator == BranchIndicator.GuardHolds || indicator == BranchIndicator.GuardFails) ? ProofUtil.Apply("rule guardHint") : null,
               ProofUtil.Apply("rule cfgDoesntFail, simp"),
               ProofUtil.Apply("rule cfgSatisfiesPosts, blast"),
               ProofUtil.Apply(ProofUtil.Repeat(ProofUtil.Simp())),
               mappingBigBlockToLocalLemmaDecl.ContainsKey(startingBigBlock) ? ProofUtil.Apply("simp add: " + nodeId + "") : null,
               mappingBigBlockToLocalLemmaDecl.ContainsKey(startingBigBlock) ? ProofUtil.Apply("rule " + nameLemmaLocal + "") : null,
               mappingBigBlockToLocalLemmaDecl.ContainsKey(startingBigBlock) ? ProofUtil.Apply("simp add: " + bigblockId + "_def") : null,
               mappingBigBlockToLocalLemmaDecl.ContainsKey(startingBigBlock) ? ProofUtil.Apply(ProofUtil.Repeat(ProofUtil.Simp())) : null,
               entryGuard != null && (indicator == BranchIndicator.GuardHolds || indicator == BranchIndicator.GuardFails) ? ProofUtil.Apply("rule guardHint") : null,
               //personalGuard != null ? ProofUtil.Apply("erule disjE") : null,
               //personalGuard == null ? ProofUtil.Apply("erule disjE, simp") : null,
               //personalGuard == null ? ProofUtil.Apply("erule disjE, simp") : null,
               //personalGuard == null ? ProofUtil.Apply("rule disjE, simp") : null,
             
               ProofUtil.Apply(ProofUtil.Repeat("erule allE[where x = " + succUniqueIntLabel + "]")),
               ProofUtil.Apply(ProofUtil.Repeat("simp add: " + outEdgesId)),
               ProofUtil.Apply("simp add: member_rec(1)"),
               ProofUtil.Apply("rule " + nameLemmaSucc + ""),
               ProofUtil.Apply("simp add: " + succBigBlockId + "_def " + contId + "_def "+ successorContId + "_def"),
               "apply blast+",
             
               proofGenInfo.GetMappingBigBlockToLoopBigBlock().ContainsKey(correspondingBigBlockOrig) ? ProofUtil.Apply("rule loop_IH_prove") : null,
               proofGenInfo.GetMappingBigBlockToLoopBigBlock().ContainsKey(correspondingBigBlockOrig) ? ProofUtil.Apply("rule loop_IH_apply") : null,
               proofGenInfo.GetMappingBigBlockToLoopBigBlock().ContainsKey(correspondingBigBlockOrig) ? ProofUtil.Apply("rule inductionHypothesis") : null,
               proofGenInfo.GetMappingBigBlockToLoopBigBlock().ContainsKey(correspondingBigBlockOrig) ? ProofUtil.Apply("rule less_trans_inv") : null,
               proofGenInfo.GetMappingBigBlockToLoopBigBlock().ContainsKey(correspondingBigBlockOrig) ? ProofUtil.Apply(ProofUtil.Repeat(ProofUtil.Simp())) : null,
             
               "done",
               "qed",
             };
           }
           return proofMethods;
        }

        private List<string> GenerateIfSuccessorProof(
          BigBlock startingBigBlock,
          Block relatedBlock,
          Expr personalGuard,
          Expr entryGuard,
          BranchIndicator indicator,
          ProofGenInfo proofGenInfo)
        {
          string bigblockId = beforeCfgProgAccess.BigBlockInfo().CmdsQualifiedName(startingBigBlock).First();
          string blockId = afterCfgProgAccess.BlockInfo().getTheoryName() + ".block_" +
                           afterCfg.GetUniqueIntLabel(relatedBlock);
          string nodeId = afterCfgProgAccess.BlockInfo().getTheoryName() + ".node_" +
                          afterCfg.GetUniqueIntLabel(relatedBlock);
          string outEdgesId = afterCfgProgAccess.BlockInfo().getTheoryName() + ".outEdges_" +
                              afterCfg.GetUniqueIntLabel(relatedBlock);

          BigBlock correspondingBigBlockOrig = proofGenInfo.GetMappingCopyBigblockToOrigBigblock()[startingBigBlock];

          IfCmd _if = (IfCmd) correspondingBigBlockOrig.ec;
          BigBlock thenBranchOrig = _if.thn.BigBlocks.First();
          BigBlock thenBranchCopy = proofGenInfo.GetMappingOrigBigblockToCopyBigblock()[thenBranchOrig];
          string thenBranchId = beforeCfgProgAccess.BigBlockInfo().CmdsQualifiedName(thenBranchCopy).First();
          string thenBranchContId = "cont_" + (proofGenInfo.GetMappingCopyBigBlockToIndex()[thenBranchCopy]);
          string nameLemmaThen = mappingBigBlockToGlobalLemmaDecl[thenBranchCopy].Name;

          string nameLemmaElse = "noLemmaElse";
          if (_if.elseBlock != null)
          {
            BigBlock elseBranchOrig = _if.elseBlock.BigBlocks.First();
            BigBlock elseBranchCopy = proofGenInfo.GetMappingOrigBigblockToCopyBigblock()[elseBranchOrig];
            string elseBranchId = beforeCfgProgAccess.BigBlockInfo().CmdsQualifiedName(elseBranchCopy).First();
            string elseBranchContId = "cont_" + (proofGenInfo.GetMappingCopyBigBlockToIndex()[elseBranchCopy]);
            nameLemmaElse = mappingBigBlockToGlobalLemmaDecl[elseBranchCopy].Name; 
          }
        
          var proofMethods = new List<string>();
          IEnumerable<Block> successors = afterCfg.GetSuccessorBlocks(relatedBlock);
          if (successors != null && successors.Any())
          {
            Block succ = successors.First();
            Block succ2 = successors.Last();
            int succUniqueIntLabel = afterCfg.GetUniqueIntLabel(succ);
            int succUniqueIntLabel2 = afterCfg.GetUniqueIntLabel(succ2);

            string contId = "cont_" + proofGenInfo.GetMappingCopyBigBlockToIndex()[startingBigBlock];
            string nameLemmaLocal = null;
          
            if (mappingBigBlockToLocalLemmaDecl.ContainsKey(startingBigBlock))
            {
              nameLemmaLocal = mappingBigBlockToLocalLemmaDecl[startingBigBlock].Name; 
            }

            var beginningOfProof = new List<string>
            {
              "proof -",
              "show ?thesis",
              ProofUtil.Apply("rule block_global_rel_if_successor"),
              startingBigBlock.simpleCmds.Any() ? 
                (indicator == BranchIndicator.GuardHolds || indicator == BranchIndicator.GuardFails ? 
                  ProofUtil.Apply("rule Rel_Main_test[of " + bigblockId + "]") : ProofUtil.Apply("rule Rel_Main_test[of " + bigblockId + " _ " + blockId + "]")) :
                ProofUtil.Apply("rule Rel_Invs[of " + bigblockId + "]"),
              ProofUtil.Apply("simp add: " + blockId + "_def " + bigblockId + "_def"),
              startingBigBlock.simpleCmds.Any() ? ProofUtil.Apply("simp add: " + blockId + "_def") : null,
              ProofUtil.Apply("rule astTrace"),
              ProofUtil.Apply("simp add: " + bigblockId + "_def"),
              ProofUtil.Apply("rule " + nodeId + "")
            };

            var middlePartOfProof = new List<string>
            {
              entryGuard == null ? ProofUtil.Apply("rule disjI1") : null,
              
              entryGuard != null ? (indicator == BranchIndicator.NoGuard ? ProofUtil.Apply("rule disjI1") : ProofUtil.Apply("rule disjI2")) : null,
              entryGuard != null && indicator == BranchIndicator.GuardHolds ? ProofUtil.Apply("rule disjI1") : null,
              entryGuard != null && indicator == BranchIndicator.GuardFails ? ProofUtil.Apply("rule disjI2") : null,
              ProofUtil.Apply("simp add: " + blockId + "_def"),
              entryGuard != null && (indicator == BranchIndicator.GuardHolds || indicator == BranchIndicator.GuardFails) ? ProofUtil.Apply("rule conjI") : null,
              entryGuard != null && (indicator == BranchIndicator.GuardHolds || indicator == BranchIndicator.GuardFails) ? ProofUtil.Apply(ProofUtil.Simp()) : null,
              entryGuard != null && (indicator == BranchIndicator.GuardHolds || indicator == BranchIndicator.GuardFails) ? ProofUtil.Apply("rule conjI") : null,
              entryGuard != null && (indicator == BranchIndicator.GuardHolds || indicator == BranchIndicator.GuardFails) ? ProofUtil.Apply(ProofUtil.Simp()) : null,
              entryGuard != null && (indicator == BranchIndicator.GuardFails) ? ProofUtil.Apply("rule conjI") : null,
              entryGuard != null && (indicator == BranchIndicator.GuardFails) ? ProofUtil.Apply("" + NegationRule(entryGuard) + "") : null,
              entryGuard != null && (indicator == BranchIndicator.GuardHolds || indicator == BranchIndicator.GuardFails) ? ProofUtil.Apply("rule guardHint") : null,
              ProofUtil.Apply("rule cfgDoesntFail, simp"),
              ProofUtil.Apply("rule cfgSatisfiesPosts, blast"),
              ProofUtil.Apply(ProofUtil.Repeat(ProofUtil.Simp())),
              mappingBigBlockToLocalLemmaDecl.ContainsKey(startingBigBlock) ? ProofUtil.Apply("simp add: " + nodeId + "") : null,
              mappingBigBlockToLocalLemmaDecl.ContainsKey(startingBigBlock) ? ProofUtil.Apply("rule " + nameLemmaLocal + "") : null,
              mappingBigBlockToLocalLemmaDecl.ContainsKey(startingBigBlock) ? ProofUtil.Apply("simp add: " + bigblockId + "_def") : null,
              mappingBigBlockToLocalLemmaDecl.ContainsKey(startingBigBlock) ? ProofUtil.Apply(ProofUtil.Repeat(ProofUtil.Simp())) : null,
              entryGuard != null && startingBigBlock.simpleCmds.Any() && (indicator == BranchIndicator.GuardHolds || indicator == BranchIndicator.GuardFails) ? ProofUtil.Apply("rule guardHint") : null,
              personalGuard != null ? ProofUtil.Apply("erule disjE") : null,
              //personalGuard == null ? ProofUtil.Apply("erule disjE, simp") : null,
              //personalGuard == null ? ProofUtil.Apply("erule disjE, simp") : null,
              personalGuard == null ? ProofUtil.Apply("rule disjE, simp") : null
            };

            var finalPartOfProof = new List<string>
            {
              ProofUtil.Apply(ProofUtil.Repeat("erule allE[where x = " + succUniqueIntLabel + "]")),
              ProofUtil.Apply(ProofUtil.Repeat("simp add: " + outEdgesId)),
              ProofUtil.Apply("simp add: member_rec(1)"),
              ProofUtil.Apply("rule conjE"),
              ProofUtil.Apply(ProofUtil.Repeat(ProofUtil.Simp())),
              ProofUtil.Apply("rule " + nameLemmaThen + ""),
              ExpandDefinitions(contId, startingBigBlock, proofGenInfo, BranchIndicator.GuardHolds),
              "apply blast+",
              proofGenInfo.GetMappingBigBlockToLoopBigBlock().ContainsKey(correspondingBigBlockOrig) ? ProofUtil.Apply("rule loop_IH_prove") : null,
              proofGenInfo.GetMappingBigBlockToLoopBigBlock().ContainsKey(correspondingBigBlockOrig) ? ProofUtil.Apply("rule loop_IH_apply") : null,
              proofGenInfo.GetMappingBigBlockToLoopBigBlock().ContainsKey(correspondingBigBlockOrig) ? ProofUtil.Apply("rule inductionHypothesis") : null,
              proofGenInfo.GetMappingBigBlockToLoopBigBlock().ContainsKey(correspondingBigBlockOrig) ? ProofUtil.Apply("rule less_trans_inv") : null,
              proofGenInfo.GetMappingBigBlockToLoopBigBlock().ContainsKey(correspondingBigBlockOrig) ? ProofUtil.Apply(ProofUtil.Repeat(ProofUtil.Simp())) : null,
              personalGuard != null && !proofGenInfo.GetMappingBigBlockToLoopBigBlock().ContainsKey(correspondingBigBlockOrig) ? 
                ProofUtil.Apply(ProofUtil.Simp()) : null,

              ProofUtil.Apply(ProofUtil.Repeat("erule allE[where x = " + succUniqueIntLabel2 + "]")),
              ProofUtil.Apply(ProofUtil.Repeat("simp add: " + outEdgesId)),
              ProofUtil.Apply("simp add: member_rec(1)"),
              ProofUtil.Apply("rule conjE"),
              ProofUtil.Apply(ProofUtil.Repeat(ProofUtil.Simp())),
              ProofUtil.Apply("rule " + nameLemmaElse + ""),
              ExpandDefinitions(contId, startingBigBlock, proofGenInfo, BranchIndicator.GuardFails),
              "apply blast+",
              proofGenInfo.GetMappingBigBlockToLoopBigBlock().ContainsKey(correspondingBigBlockOrig) ? ProofUtil.Apply("rule loop_IH_prove") : null,
              proofGenInfo.GetMappingBigBlockToLoopBigBlock().ContainsKey(correspondingBigBlockOrig) ? ProofUtil.Apply("rule loop_IH_apply") : null,
              proofGenInfo.GetMappingBigBlockToLoopBigBlock().ContainsKey(correspondingBigBlockOrig) ? ProofUtil.Apply("rule inductionHypothesis") : null,
              proofGenInfo.GetMappingBigBlockToLoopBigBlock().ContainsKey(correspondingBigBlockOrig) ? ProofUtil.Apply("rule less_trans_inv") : null,
              proofGenInfo.GetMappingBigBlockToLoopBigBlock().ContainsKey(correspondingBigBlockOrig) ? ProofUtil.Apply(ProofUtil.Repeat(ProofUtil.Simp())) : null,

              "done",
              "qed"
            };
            
            proofMethods.AddRange(beginningOfProof);
            proofMethods.AddRange(middlePartOfProof);
            proofMethods.AddRange(finalPartOfProof);
          }
          return proofMethods;
        }
    }
}