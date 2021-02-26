using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.BoogieIsaInterface.VariableTranslation;
using ProofGeneration.Isa;
using ProofGeneration.Util;
using ProofGeneration.VCProofGen;

namespace ProofGeneration.ProgramToVCProof
{
    internal class VcPhaseLemmaManager : ILocaleContext
    {
        private readonly AssumptionManager assmManager;

        private readonly BoogieContextIsa boogieContext;

        private readonly IDictionary<NamedDeclaration, Term> declToVCMapping;
        private readonly TermIdent finalNode = IsaCommonTerms.TermIdentFromName("m'");
        private readonly TermIdent finalState = IsaCommonTerms.TermIdentFromName("s'");
        private readonly IDictionary<Function, TermIdent> funToInterpMapping;

        private readonly string globalAssmsName = "global_assms";
        private readonly Term initState;

        private readonly IsaBlockInfo isaBlockInfo;

        private readonly BoogieMethodData methodData;

        private readonly TermIdent normalInitState = IsaCommonTerms.TermIdentFromName("n_s");
        private readonly IEnumerable<Variable> programVariables;

        private readonly IsaUniqueNamer uniqueNamer = new IsaUniqueNamer();

        private readonly IVariableTranslationFactory variableFactory;
        private readonly VCInstantiation<Block> vcinst;

        public VcPhaseLemmaManager(VCInstantiation<Block> vcinst,
            BoogieMethodData methodData,
            IEnumerable<Function> vcFunctions,
            IsaBlockInfo isaBlockInfo,
            IVariableTranslationFactory variableFactory)
        {
            this.vcinst = vcinst;
            this.methodData = methodData;
            programVariables = methodData.AllVariables();
            initState = IsaBoogieTerm.Normal(normalInitState);
            this.isaBlockInfo = isaBlockInfo;
            this.variableFactory = variableFactory;
            boogieContext = new BoogieContextIsa(
                IsaCommonTerms.TermIdentFromName("A"),
                IsaCommonTerms.TermIdentFromName("M"),
                IsaCommonTerms.TermIdentFromName("\\<Lambda>"),
                IsaCommonTerms.TermIdentFromName("\\<Gamma>"),
                IsaCommonTerms.TermIdentFromName("\\<Omega>")
            );
            var typeDeclTranslation = new ConcreteTypeDeclTranslation(boogieContext);
            declToVCMapping = LemmaHelper.DeclToTerm(
                ((IEnumerable<NamedDeclaration>) methodData.Functions).Union(programVariables),
                vcFunctions,
                typeDeclTranslation,
                uniqueNamer);
            //separate unique namer for function interpretations (since they already have a name in uniqueNamer): possible clashes
            funToInterpMapping = LemmaHelper.FunToTerm(methodData.Functions, new IsaUniqueNamer());

            assmManager = new AssumptionManager(methodData.Functions, programVariables, variableFactory);
        }


        public ContextElem Context()
        {
            return new ContextElem(
                ContextHelper.GlobalFixedVariables(boogieContext, methodData.Functions, programVariables,
                    normalInitState, funToInterpMapping, uniqueNamer),
                assmManager.AllAssumptions(funToInterpMapping, declToVCMapping, normalInitState, boogieContext,
                    variableFactory.CreateTranslation().VarTranslation),
                assmManager.AllAssumptionLabels()
            );
        }

        public IList<OuterDecl> Prelude()
        {
            var assmLabels = assmManager.AllAssumptionLabels();
            var globalAssmsLemmas = new LemmasDecl(globalAssmsName, assmLabels);

            var closedAssm = assmManager.GetAssumptionLabel(AssumptionManager.SpecialAssumptionsKind.TypeValClosed);

            var forallPolyThm =
                new LemmasDecl("forall_poly_thm", new List<string> {"forall_vc_type[OF " + closedAssm + "]"});
            var existsPolyThm =
                new LemmasDecl("exists_poly_thm", new List<string> {"exists_vc_type[OF " + closedAssm + "]"});

            // if One_nat_def is not removed from the simpset, then there is an issue with the assumption "ns 1 = ...",
            // since Isabelle rewrites it to Suc 0 and a subsequent step in the proof may fail
            var decl = new DeclareDecl("Nat.One_nat_def[simp del]");

            return new List<OuterDecl> {globalAssmsLemmas, forallPolyThm, existsPolyThm, decl};
        }

        public LemmaDecl GenerateBlockLemma(Block block, Block finalCfgBlock, IEnumerable<Block> finalCfgSuccessors,
            string lemmaName, string vcHintsName)
        {
            var cmdsReduce = IsaBoogieTerm.RedCmdList(boogieContext,
                IsaCommonTerms.TermIdentFromName(isaBlockInfo.CmdsQualifiedName(block)),
                initState, finalState);

            var vcAssm = vcinst.GetVCObjInstantiation(finalCfgBlock, declToVCMapping);

            //do not use separate assumption, leads to issues
            var conclusion = ConclusionBlock(finalCfgSuccessors, normalInitState, finalState, declToVCMapping, vcinst,
                LemmaHelper.FinalStateIsMagic(block));

            Term statement = TermBinary.MetaImplies(cmdsReduce, TermBinary.MetaImplies(vcAssm, conclusion));

            var proof = BlockCorrectProof(block, finalCfgBlock, vcHintsName);

            return new LemmaDecl(lemmaName, ContextElem.CreateEmptyContext(), statement, proof);
        }

        public LemmaDecl GenerateCfgLemma(
            Block block,
            Block finalCfgBlock,
            bool isContainedInFinalCfg,
            IEnumerable<Block> successors,
            IEnumerable<Block> finalCfgSuccessors,
            Term cfg,
            Func<Block, string> cfgLemmaName,
            LemmaDecl BlockLemma)
        {
            var red = IsaBoogieTerm.RedCFGMulti(
                boogieContext,
                cfg,
                IsaBoogieTerm.CFGConfigNode(new NatConst(isaBlockInfo.BlockIds[block]),
                    IsaBoogieTerm.Normal(normalInitState)),
                IsaBoogieTerm.CFGConfig(finalNode, finalState));
            var assumption = new List<Term> {red};
            var hasVcAssm = false;
            if (isContainedInFinalCfg)
            {
                assumption.Add(vcinst.GetVCObjInstantiation(finalCfgBlock, declToVCMapping));
                hasVcAssm = true;
            }
            else
            {
                //vc assumption is conjunction of reachable successors in final cfg
                if (finalCfgSuccessors.Any())
                {
                    assumption.Add(
                        LemmaHelper.ConjunctionOfSuccessorBlocks(finalCfgSuccessors, declToVCMapping, vcinst));
                    hasVcAssm = true;
                }
            }

            Term conclusion = new TermBinary(finalState, IsaBoogieTerm.Failure(), TermBinary.BinaryOpCode.NEQ);

            var nodeLemma = isaBlockInfo.BlockCmdsMembershipLemma(block);
            var outEdgesLemma = isaBlockInfo.OutEdgesMembershipLemma(block);
            var proofMethods = new List<string>();


            var eruleLocalBlock =
                "erule " + (hasVcAssm ? ProofUtil.OF(BlockLemma.name, "_", "assms(2)") : BlockLemma.name);

            if (isContainedInFinalCfg && LemmaHelper.FinalStateIsMagic(block))
            {
                proofMethods.Add("apply (rule converse_rtranclpE2[OF assms(1)], fastforce)");
                proofMethods.Add(ProofUtil.Apply("rule " +
                                                 ProofUtil.OF("red_cfg_multi_backwards_step_magic", "assms(1)",
                                                     nodeLemma)));
                proofMethods.Add(ProofUtil.By(eruleLocalBlock));
                return new LemmaDecl(cfgLemmaName(block), ContextElem.CreateWithAssumptions(assumption), conclusion,
                    new Proof(proofMethods));
            }

            if (successors.Any())
            {
                proofMethods.Add("apply (rule converse_rtranclpE2[OF assms(1)], fastforce)");
                var cfg_lemma = finalCfgSuccessors.Any()
                    ? "red_cfg_multi_backwards_step"
                    : "red_cfg_multi_backwards_step_2";

                proofMethods.Add(ProofUtil.Apply("rule " +
                                                 ProofUtil.OF(cfg_lemma, "assms(1)", nodeLemma)));
                proofMethods.Add(ProofUtil.Apply(eruleLocalBlock));
                proofMethods.Add("apply (" + ProofUtil.Simp(outEdgesLemma) + ")");
                foreach (var bSuc in successors)
                {
                    proofMethods.Add("apply (erule member_elim, simp)");
                    proofMethods.Add("apply (erule " + cfgLemmaName(bSuc) + ", simp?" + ")");
                }

                proofMethods.Add("by (simp add: member_rec(2))");
            }
            else
            {
                proofMethods.Add("apply (rule converse_rtranclpE2[OF assms(1)], fastforce)");
                proofMethods.Add("apply (rule " + ProofUtil.OF("red_cfg_multi_backwards_step_no_succ", "assms(1)",
                    nodeLemma, outEdgesLemma) + ")");
                if (isContainedInFinalCfg)
                    proofMethods.Add("using " + ProofUtil.OF(BlockLemma.name, "_", "assms(2)") + " by blast");
                else
                    proofMethods.Add("using " + BlockLemma.name + " by blast");
            }

            return new LemmaDecl(cfgLemmaName(block), ContextElem.CreateWithAssumptions(assumption), conclusion,
                new Proof(proofMethods));
        }

        public LemmaDecl GenerateEmptyBlockLemma(Block block, IEnumerable<Block> finalCfgSuccessors, string lemmaName)
        {
            //Term cmds = new TermList(cmdIsaVisitor.Translate(block.Cmds));
            var blockDefName = isaBlockInfo.CmdsQualifiedName(block);
            Term blockDefTerm = IsaCommonTerms.TermIdentFromName(blockDefName);
            var cmdsReduce = IsaBoogieTerm.RedCmdList(boogieContext, blockDefTerm, initState, finalState);
            var assumptions = new List<Term> {cmdsReduce};
            if (finalCfgSuccessors.Any())
                assumptions.Add(LemmaHelper.ConjunctionOfSuccessorBlocks(finalCfgSuccessors, declToVCMapping, vcinst));

            var conclusion = ConclusionBlock(finalCfgSuccessors, normalInitState, finalState, declToVCMapping, vcinst);

            var proof = new Proof(
                new List<string>
                {
                    "using assms",
                    "unfolding " + blockDefName + "_def",
                    "apply cases",
                    "by auto"
                }
            );

            return new LemmaDecl(lemmaName, ContextElem.CreateWithAssumptions(assumptions), conclusion, proof);
        }

        private Proof BlockCorrectProof(Block block, Block finalCfgBlock, string vcHintsName)
        {
            List<string> methods;
            if (vcHintsName == null)
                methods = new List<string>
                {
                    "apply (erule red_cmd_list.cases)",
                    "using " + globalAssmsName,
                    "unfolding " + isaBlockInfo.CmdsQualifiedName(block) + "_def " +
                    vcinst.GetVCObjNameRef(finalCfgBlock) + "_def",
                    "apply (handle_cmd_list_full?)",
                    "by (auto?)"
                };
            else
                methods = new List<string>
                {
                    "unfolding " + isaBlockInfo.CmdsQualifiedName(block) + "_def " +
                    vcinst.GetVCObjNameRef(finalCfgBlock) + "_def",
                    "apply (tactic \\<open> boogie_vc_tac @{context} @{thms " + globalAssmsName + "} " +
                    "(@{thm forall_poly_thm}, @{thm exists_poly_thm}) " + vcHintsName + " \\<close>)",
                    "by (auto?)"
                };

            return new Proof(methods);
        }

        private static Term ConclusionBlock(
            IEnumerable<Block> b_successors,
            Term normalInitState,
            Term finalState,
            IDictionary<NamedDeclaration, Term> declToVCMapping,
            VCInstantiation<Block> vcinst,
            bool useMagicFinalState = false)
        {
            if (useMagicFinalState)
                return new TermBinary(finalState, IsaBoogieTerm.Magic(), TermBinary.BinaryOpCode.EQ);

            Term nonFailureConclusion =
                new TermBinary(finalState, IsaBoogieTerm.Failure(), TermBinary.BinaryOpCode.NEQ);

            var normalFinalState = IsaCommonTerms.TermIdentFromName("n_s'");

            Term ifNormalConclusionLhs = new TermBinary(finalState, IsaBoogieTerm.Normal(normalFinalState),
                TermBinary.BinaryOpCode.EQ);

            Term ifNormalConclusionRhs1 = new TermBinary(normalFinalState, normalInitState, TermBinary.BinaryOpCode.EQ);

            var ifNormalConclusionRhs =
                !b_successors.Any()
                    ? ifNormalConclusionRhs1
                    : new TermBinary(
                        ifNormalConclusionRhs1,
                        LemmaHelper.ConjunctionOfSuccessorBlocks(b_successors, declToVCMapping, vcinst),
                        TermBinary.BinaryOpCode.AND);

            Term ifNormalConclusion =
                new TermQuantifier(
                    TermQuantifier.QuantifierKind.ALL,
                    new List<Identifier> {normalFinalState.id},
                    new TermBinary(
                        ifNormalConclusionLhs,
                        ifNormalConclusionRhs,
                        TermBinary.BinaryOpCode.IMPLIES)
                );

            return new TermBinary(nonFailureConclusion, ifNormalConclusion, TermBinary.BinaryOpCode.AND);
        }
    }
}