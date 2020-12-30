using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.BoogieIsaInterface.VariableTranslation;
using ProofGeneration.Isa;
using ProofGeneration.Util;

namespace ProofGeneration.CfgToDag
{
    public class CfgToDagLemmaManager
    {
        private readonly IProgramAccessor beforeDagProgAccess;
        private readonly IProgramAccessor afterDagProgAccess;
        private readonly IVariableTranslation<Variable> variableTranslation;
        
        private readonly CfgToDagHintManager hintManager;
        private readonly IDictionary<Block, IList<Block>> blocksToLoops;
        private readonly IDictionary<Block, Block> beforeToAfterBlock;
        
        private readonly BasicCmdIsaVisitor basicCmdIsaVisitor;
        private readonly BoogieContextIsa boogieContext;

        private readonly Term normalInitState1 = IsaCommonTerms.TermIdentFromName("ns1");
        private readonly Term normalInitState2 = IsaCommonTerms.TermIdentFromName("ns2");
        private readonly Term initState1;
        private readonly Term initState2;
        private readonly Term finalState = IsaCommonTerms.TermIdentFromName("s'");
        private readonly TermIdent finalNode = IsaCommonTerms.TermIdentFromName("m'");

        private readonly string redCfgName = "Red";
        private readonly string dagVerifiesName = "DagVerifies";
        private readonly string dagAssmsName = "dagAssmsName";
        
        private readonly IsaUniqueNamer namer = new IsaUniqueNamer();
        
        public CfgToDagLemmaManager(
            IProgramAccessor beforeDagProgAccess,
            IProgramAccessor afterDagProgAccess,
            string varContextName,
            CfgToDagHintManager hintManager,
            IDictionary<Block, IList<Block>> blocksToLoops,
            IDictionary<Block, Block> beforeToAfterBlock,
            IVariableTranslationFactory varFactory
        )
        {
            this.beforeDagProgAccess = beforeDagProgAccess;
            this.afterDagProgAccess = afterDagProgAccess;
            variableTranslation = varFactory.CreateTranslation().VarTranslation;
            this.hintManager = hintManager;
            this.blocksToLoops = blocksToLoops;
            this.beforeToAfterBlock = beforeToAfterBlock;
            boogieContext = new BoogieContextIsa(
                IsaCommonTerms.TermIdentFromName("A"),
                IsaCommonTerms.TermIdentFromName("M"),
                IsaCommonTerms.TermIdentFromName(varContextName),
                IsaCommonTerms.TermIdentFromName("\\<Gamma>"),
                IsaCommonTerms.TermIdentFromName("\\<Omega>"));

            initState1 = IsaBoogieTerm.Normal(normalInitState1);
            initState2 = IsaBoogieTerm.Normal(normalInitState2);
            basicCmdIsaVisitor = new BasicCmdIsaVisitor(new IsaUniqueNamer(), varFactory);
        }

        private Term HavocedVarsTerm(IEnumerable<Variable> vars)
        {
           return new TermList(
               vars.Select(x =>
                    {
                        if (variableTranslation.TryTranslateVariableId(x, out Term varId, out _))
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

        /// <summary>
        /// first element of returned tuple are the lemmas for the local block proof
        /// second element of returned tuple is the CFG block proof (i.e., depends on the local lemmas)
        /// </summary>
        public Tuple<IEnumerable<LemmaDecl>,LemmaDecl> BlockLemma(
            Block beforeDag, 
            Block afterDag,
            IEnumerable<Block> successors,
            Func<Block, string> blockLemmaName,
            Func<Block, string> cfgLemmaName,
            bool singleEdgeCut)
        {
            string beforeCmdsDefName = beforeDagProgAccess.BlockInfo().CmdsQualifiedName(beforeDag);
            Term beforeCmds = IsaCommonTerms.TermIdentFromName(beforeCmdsDefName);
            string afterCmdsDefName = afterDagProgAccess.BlockInfo().CmdsQualifiedName(afterDag);
            Term afterCmds = IsaCommonTerms.TermIdentFromName(afterCmdsDefName);
            
            var finalNodeId2 = new SimpleIdentifier("m2'");
            Term finalNode2 = new TermIdent(finalNodeId2);
            var finalStateId2 = new SimpleIdentifier("s2'");
            Term finalState2 = new TermIdent(finalStateId2);

            Term preInvs;
            Term havocedVars;
            if (hintManager.IsLoopHead(beforeDag, out LoopHeadHint blockHeadHint))
            {
                preInvs = InvariantsTerm(blockHeadHint.Invariants);
                havocedVars = HavocedVarsTerm(blockHeadHint.ModifiedVars);
            }
            else
            {
                preInvs = IsaCommonTerms.EmptyList;
                havocedVars = IsaCommonTerms.EmptyList;
            }

            var postInvsList = new List<Term>();
            foreach (var bSuc in successors)
            {
                if(hintManager.IsLoopHead(bSuc, out LoopHeadHint hint))
                {
                    postInvsList.AddRange(hint.Invariants.Select(inv => basicCmdIsaVisitor.Translate(inv)));
                }
            }
            
            var postInvs = new TermList(postInvsList);

            #region local block lemma
            List<Term> assumptions = new List<Term>
            {
                IsaBoogieTerm.RedCmdList(boogieContext, beforeCmds, initState1, finalState),
            };

            Term dagVerifiesAssm =
                TermQuantifier.MetaAll(
                    new List<Identifier> {finalStateId2},
                    null,
                    TermBinary.MetaImplies(
                        IsaBoogieTerm.RedCmdList(boogieContext, afterCmds, initState2, finalState2),
                        TermBinary.Neq(finalState2, IsaBoogieTerm.Failure()))
                );
            assumptions.Add(dagVerifiesAssm);
            
            Term dagLemmaAssm = BlockLemmaAssumption(
                boogieContext,
                havocedVars,
                preInvs);
            assumptions.Add(dagLemmaAssm);

            Term conclusion= 
                BlockLemmaConclusion(
                boogieContext,
                postInvs,
                afterCmds,
                singleEdgeCut);

            var proofMethods = new List<string>
            {
                "using assms",
                "apply (rule dag_rel_block_lemma_compact, simp)",
                "unfolding " + beforeCmdsDefName + "_def " + afterCmdsDefName + "_def",
                "apply cfg_dag_rel_tac_single+",
                "apply simp"
            };

            if (blockHeadHint != null)
            {
                foreach (var x in blockHeadHint.ModifiedVars)
                {
                    proofMethods.Add(ProofUtil.Apply(ProofUtil.Simp(beforeDagProgAccess.LookupVarTyLemma(x))));
                }
            }
            
            //TODO proof that post invariants reduce to booleans
            proofMethods.Add("subgoal");
            proofMethods.Add("sorry");
            proofMethods.Add("done");
            
            var blockLemma = new LemmaDecl(
                    blockLemmaName(beforeDag), 
                    ContextElem.CreateWithAssumptions(assumptions), 
                    conclusion,
                    new Proof(proofMethods)
                );
            #endregion
            
            #region cfg lemma

            Term numSteps = IsaCommonTerms.TermIdentFromName("j");
            
            
            Term redCfg = IsaBoogieTerm.RedCFGKStep(
                boogieContext,
                beforeDagProgAccess.CfgDecl(),
                IsaBoogieTerm.CFGConfigNode(new NatConst(beforeDagProgAccess.BlockInfo().BlockIds[beforeDag]),
                    IsaBoogieTerm.Normal(normalInitState1)),
                numSteps,
                IsaBoogieTerm.CFGConfig(finalNode, finalState));
            
            var cfgAssumptions = new List<Term> { 
                redCfg,
                dagLemmaAssm
            };

            Term dagVerifiesCfgAssm =
                TermQuantifier.MetaAll(
                    new List<Identifier> {finalNodeId2, finalStateId2},
                    null,
                    TermBinary.MetaImplies(
                        IsaBoogieTerm.RedCFGMulti(boogieContext, afterDagProgAccess.CfgDecl(),
                            IsaBoogieTerm.CFGConfigNode(
                                new NatConst(afterDagProgAccess.BlockInfo().BlockIds[afterDag]),
                                IsaBoogieTerm.Normal(normalInitState2)
                            ),
                            IsaBoogieTerm.CFGConfig(finalNode2, finalState2)
                        ),
                        TermBinary.Neq(finalState2, IsaBoogieTerm.Failure()))
                );
            
            cfgAssumptions.Add(dagVerifiesCfgAssm);
            

            var cfgAssumptionNames = new List<string>
            {
                redCfgName, dagAssmsName, dagVerifiesName
            };
            
            foreach (Block loopBlock in blocksToLoops[beforeDag])
            {
                var hint = hintManager.GetLoopHead(loopBlock);
                var inductionHyp = LoopIndHypAssumption(
                    boogieContext,
                    beforeDagProgAccess.CfgDecl(),
                    HavocedVarsTerm(hint.ModifiedVars),
                    InvariantsTerm(hint.Invariants),
                    normalInitState1,
                    new NatConst(beforeDagProgAccess.BlockInfo().BlockIds[loopBlock]),
                    numSteps);
                
                cfgAssumptions.Add(inductionHyp);
                cfgAssumptionNames.Add(LoopIndHypName(loopBlock));
            }

            Proof cfgProof;
            if (blockHeadHint == null)
            {
                cfgProof = GenerateProofNonLoopHead(beforeDag, afterDag, blockLemmaName, cfgLemmaName, successors);
            }
            else
            {
                cfgProof =
                    new Proof(
                    new List<string>
                    {
                        "sorry"
                    }
                );
            }
            
            LemmaDecl cfgLemma = new LemmaDecl(
                cfgLemmaName(beforeDag),
                ContextElem.CreateWithAssumptions(cfgAssumptions, cfgAssumptionNames), 
                TermBinary.Neq(finalState, IsaBoogieTerm.Failure()),
                cfgProof
            );
            
            #endregion

            var localLemmas = new List<LemmaDecl>();
            localLemmas.Add(blockLemma);

            var loops = blocksToLoops[beforeDag];
            
            //TODO: if the loop is within multiple loops, need to find the most inner one
            Block loopMod = null;
            if (loops.Any())
            {
                loopMod = loops.First();
            }
            if (hintManager.IsLoopHead(beforeDag, out _))
            {
                loopMod = beforeDag;
            }
                
            if(loopMod != null)
            {
                var hint = hintManager.GetLoopHead(loopMod);
                localLemmas.Add(BlockModVarsLemma(BlockModVarsLemmaName(beforeDag), beforeCmds, beforeCmdsDefName, HavocedVarsTerm(hint.ModifiedVars))); 
            }

            return new Tuple<IEnumerable<LemmaDecl>, LemmaDecl>(localLemmas, cfgLemma);
        }

        private LemmaDecl BlockModVarsLemma(string lemmaName, Term cmds, string cmdsDef, Term modVarsList)
        {
            Term statement = 
                new TermApp(
                IsaCommonTerms.TermIdentFromName("mods_contained_in"),
                IsaCommonTerms.SetOfList(modVarsList),
                cmds);

            Proof proof =
                new Proof(
                    new List<string>
                    {
                        "unfolding " + cmdsDef + "_def",
                        "by simp"
                    }
                );

            return new LemmaDecl(lemmaName, statement, proof);
        }

        private Proof GenerateProofNonLoopHead(
            Block beforeBlock, 
            Block afterBlock, 
            Func <Block, string> blockLemmaName,
            Func<Block, string> cfgLemmaName,
            IEnumerable<Block> successors)
        {
            var sb = new StringBuilder();
            var loops = blocksToLoops[beforeBlock];
            var helperThm = loops.Any() ? "cfg_dag_helper_2" : "cfg_dag_helper_1";

            sb.AppendLine(ProofUtil.Apply(
                ProofUtil.Rule(
                    ProofUtil.OF(helperThm, redCfgName, "_","_", dagVerifiesName, dagAssmsName))));
            sb.AppendLine(ProofUtil.Apply(ProofUtil.Rule(beforeDagProgAccess.BlockInfo()
                .BlockCmdsMembershipLemma(beforeBlock))));
            sb.AppendLine(ProofUtil.Apply(ProofUtil.Rule(afterDagProgAccess.BlockInfo()
                .BlockCmdsMembershipLemma(afterBlock))));
            sb.AppendLine(ProofUtil.Apply("assumption+"));
            sb.AppendLine(ProofUtil.Apply("rule " + blockLemmaName(beforeBlock)));
            sb.AppendLine(ProofUtil.Apply("assumption+"));
            
            if (loops.Any())
                sb.AppendLine(ProofUtil.Apply(ProofUtil.Rule(BlockModVarsLemmaName(beforeBlock))));

            sb.AppendLine(
                ProofUtil.Apply(ProofUtil.Simp(beforeDagProgAccess.BlockInfo().OutEdgesMembershipLemma(beforeBlock))));
            
            /* handle each successor
             * assume that the edge list in embedding coincides with the iteration order of the successors
             */
            foreach (Block bSuc in successors)
            {
                sb.AppendLine(ProofUtil.Apply("erule member_elim"));
                if (loops.Contains(bSuc))
                {
                    //backedge --> need to apply IH
                    sb.AppendLine(ProofUtil.Apply(ProofUtil.Rule("loop_ih_apply[where ?j'=\"j-1\"]")));
                    sb.AppendLine(ProofUtil.Apply(ProofUtil.Rule(LoopIndHypName(bSuc))));
                    sb.AppendLine(ProofUtil.Apply("simp, simp"));
                    sb.AppendLine("unfolding dag_lemma_assms_def");
                    sb.AppendLine(ProofUtil.Apply("intro conjI, simp"));
                    sb.AppendLine("using nstate_same_on_sym apply fastforce");
                    sb.AppendLine(ProofUtil.Apply("simp"));
                }
                else
                {
                    sb.AppendLine(ProofUtil.Apply("rule " + cfgLemmaName(bSuc)));
                    sb.AppendLine("apply simp");
                    sb.AppendLine("unfolding dag_lemma_assms_def");
                    sb.AppendLine("apply (intro conjI)");
                    sb.AppendLine("apply simp");
                    sb.AppendLine(hintManager.IsLoopHead(bSuc, out _)
                        ? "apply (erule nstate_same_on_empty_subset)"
                        : "apply simp");
                    sb.AppendLine("apply simp");
                    Block bSucAfter = beforeToAfterBlock[bSuc];
                    int bSucAfterId = afterDagProgAccess.BlockInfo().BlockIds[bSucAfter];
                    sb.AppendLine("apply (erule allE[where x=" + bSucAfterId + "])");
                    sb.AppendLine("apply simp");
                    sb.AppendLine(ProofUtil.Apply(
                        ProofUtil.Simp(afterDagProgAccess.BlockInfo().OutEdgesMembershipLemma(afterBlock))));
                    sb.AppendLine(ProofUtil.Apply(ProofUtil.Simp("member_rec(1)")));
                    sb.AppendLine(ProofUtil.Apply("fastforce?"));
                    //if successor is inside a subset of the loops that we the current block is in, then need to propagate the induction hypotheses
                    var loopsSuc = blocksToLoops[bSuc];
                    // we can be sure that every loop that the successor is in, the current block is in too (since the CFG is reducible)
                    foreach (var loopSuc in loopsSuc)
                    {
                        sb.AppendLine(ProofUtil.Apply("rule loop_ih_convert"));
                        sb.AppendLine("using " + LoopIndHypName(loopSuc) + " apply simp");
                        sb.AppendLine("apply simp");
                    }

                }
            }

            sb.AppendLine("by (simp add: member_rec(2))");

            return new Proof(new List<string> {sb.ToString()});
        }

        private Term BlockLemmaAssumption(
            BoogieContextIsa boogieContext,
            Term havocedVars,
            Term preInvs
        )
        {
            return new TermApp(
                IsaCommonTerms.TermIdentFromName("dag_lemma_assms"),
                boogieContext.absValTyMap,
                boogieContext.varContext,
                boogieContext.funContext,
                boogieContext.rtypeEnv,
                havocedVars,
                preInvs,
                normalInitState1,
                normalInitState2
            );
        }

        private Term BlockLemmaConclusion(
            BoogieContextIsa boogieContext,
            Term postInvs,
            Term cmds2,
            bool singleEdgeCut
        )
        {
            return new TermApp(
                IsaCommonTerms.TermIdentFromName("dag_lemma_conclusion"),
                boogieContext.absValTyMap,
                boogieContext.methodContext,
                boogieContext.varContext,
                boogieContext.funContext,
                boogieContext.rtypeEnv,
                postInvs,
                cmds2,
                normalInitState2,
                finalState,
                new BoolConst(singleEdgeCut)
            );
        }

        private Term LoopIndHypAssumption(
            BoogieContextIsa boogieContext,
            Term cfg,
            Term modVars,
            Term invs,
            Term normalState,
            Term loopHeadNode,
            Term numSteps
        )
        {
            return new TermApp(
                IsaCommonTerms.TermIdentFromName("loop_ih"),
                boogieContext.absValTyMap,
                boogieContext.methodContext,
                boogieContext.varContext,
                boogieContext.funContext,
                boogieContext.rtypeEnv,
                cfg,
                modVars,
                invs,
                normalState,
                finalState,
                loopHeadNode,
                finalNode,
                numSteps
                );
        }

        private string LoopIndHypName(Block b)
        {
            return "IH_"+namer.GetName(b, b.Label);
        }

        private string BlockModVarsLemmaName(Block b)
        {
            return "Mods_" + namer.GetName(b, b.Label);
        }
            
    }
}