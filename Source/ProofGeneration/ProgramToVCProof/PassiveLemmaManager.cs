using System;
using System.Collections;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.BoogieIsaInterface.VariableTranslation;
using ProofGeneration.CFGRepresentation;
using ProofGeneration.Isa;
using ProofGeneration.Util;
using ProofGeneration.VCProofGen;

namespace ProofGeneration.ProgramToVCProof
{
    class PassiveLemmaManager : IBlockLemmaManager
    {
        private readonly VCInstantiation<Block> vcinst;

        private readonly BoogieMethodData methodData;
        private readonly IEnumerable<Variable> programVariables;

        private readonly BoogieContextIsa boogieContext;

        private readonly TermIdent normalInitState = IsaCommonTerms.TermIdentFromName("n_s");
        private readonly Term initState;
        private readonly TermIdent finalState = IsaCommonTerms.TermIdentFromName("s'");
        private readonly TermIdent finalNode = IsaCommonTerms.TermIdentFromName("m'");

        private readonly IDictionary<NamedDeclaration, Term> declToVCMapping;
        private readonly IDictionary<Function, TermIdent> funToInterpMapping;

        private readonly MultiCmdIsaVisitor cmdIsaVisitor;

        private readonly IsaUniqueNamer uniqueNamer = new IsaUniqueNamer();

        private readonly IVariableTranslationFactory variableFactory;

        private readonly string globalAssmsName = "global_assms";

        private readonly IVCVarFunTranslator vcTranslator;

        private readonly AssumptionManager assmManager;

        private readonly IsaBlockInfo isaBlockInfo;

        public PassiveLemmaManager(VCInstantiation<Block> vcinst, 
            BoogieMethodData methodData, 
            IEnumerable<Function> vcFunctions, 
            IsaBlockInfo isaBlockInfo,
            IVCVarFunTranslator vcTranslator,
            IVariableTranslationFactory variableFactory)
        {
            this.vcinst = vcinst;
            this.methodData = methodData;
            programVariables = methodData.InParams.Union(methodData.Locals).Union(methodData.OutParams);
            initState = IsaBoogieTerm.Normal(normalInitState);
            this.isaBlockInfo = isaBlockInfo;
            this.vcTranslator = vcTranslator;
            this.variableFactory = variableFactory;
            cmdIsaVisitor = new MultiCmdIsaVisitor(uniqueNamer, variableFactory);
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

        public LemmaDecl GenerateBlockLemma(Block block, IEnumerable<Block> successors, string lemmaName, string vcHintsName)
        {
            Term cmdsReduce = IsaBoogieTerm.RedCmdList(boogieContext, IsaCommonTerms.TermIdentFromName(isaBlockInfo.CmdsQualifiedName(block)), 
                initState, finalState);

            List<Term> assumptions = new List<Term> { cmdsReduce };
            assumptions.Add(vcinst.GetVCObjInstantiation(block, declToVCMapping));

            Term conclusion = ConclusionBlock(block, successors, normalInitState, finalState, declToVCMapping, vcinst, LemmaHelper.FinalStateIsMagic(block));

            Proof proof = BlockCorrectProof(block, vcHintsName);

            return new LemmaDecl(lemmaName, ContextElem.CreateWithAssumptions(assumptions), conclusion, proof);
        }

        public LemmaDecl GenerateCfgLemma(Block block, IEnumerable<Block> successors, Term cfg, Func<Block, string> cfgLemmaName, LemmaDecl BlockLemma)
        {
            Term red = IsaBoogieTerm.RedCFGMulti(
                boogieContext,
                cfg,
                IsaBoogieTerm.CFGConfigNode(new NatConst(isaBlockInfo.BlockIds[block]),
                    IsaBoogieTerm.Normal(normalInitState)),
                IsaBoogieTerm.CFGConfig(finalNode, finalState));
            List<Term> assumption = new List<Term> { red, vcinst.GetVCObjInstantiation(block, declToVCMapping) };
            Term conclusion = new TermBinary(finalState, IsaBoogieTerm.Failure(), TermBinary.BinaryOpCode.NEQ);

            string nodeLemma = isaBlockInfo.BlockCmdsMembershipLemma(block);
            string outEdgesLemma = isaBlockInfo.OutEdgesMembershipLemma(block);
            var proofMethods = new List<string>();
            if (successors.Any())
            {
                proofMethods.Add("apply (rule converse_rtranclpE2[OF assms(1)], fastforce)");
                proofMethods.Add(ProofUtil.Apply("rule " +
                                 ProofUtil.OF("red_cfg_multi_backwards_step", "assms(1)", nodeLemma)));
                proofMethods.Add(ProofUtil.Apply("erule " + ProofUtil.OF(BlockLemma.name, "_", "assms(2)")));
                proofMethods.Add("apply (" + ProofUtil.Simp(outEdgesLemma) + ")");
                foreach (var bSuc in successors)
                {
                    proofMethods.Add("apply (erule member_elim, simp)");
                    proofMethods.Add("apply (erule " + cfgLemmaName(bSuc) + ", simp" + ")");
                }
                proofMethods.Add("by (simp add: member_rec(2))");
            }
            else
            {
                proofMethods.Add("apply (rule converse_rtranclpE2[OF assms(1)], fastforce)");
                proofMethods.Add("apply (rule " + ProofUtil.OF("red_cfg_multi_backwards_step_no_succ", "assms(1)",
                    nodeLemma, outEdgesLemma)+")");
                proofMethods.Add("using " + ProofUtil.OF(BlockLemma.name, "_", "assms(2)") + " by blast");
            }

            return new LemmaDecl(cfgLemmaName(block), ContextElem.CreateWithAssumptions(assumption), conclusion,
                new Proof(proofMethods));
        }

        public LemmaDecl GenerateEmptyBlockLemma(Block block, IEnumerable<Block> successors, string lemmaName)
        {
            Term cmds = new TermList(cmdIsaVisitor.Translate(block.Cmds));
            Term cmdsReduce = IsaBoogieTerm.RedCmdList(boogieContext, cmds, initState, finalState);

            List<Term> assumptions = new List<Term>() { cmdsReduce };
            if (successors.Any())
                assumptions.Add(LemmaHelper.ConjunctionOfSuccessorBlocks(successors, declToVCMapping, vcinst));

            Term conclusion = ConclusionBlock(block, successors, normalInitState, finalState, declToVCMapping, vcinst);

            Proof proof = new Proof(
                new List<string>()
                {
                    "using assms",
                    "apply cases",
                    "by auto"
                }
              );

            return new LemmaDecl(lemmaName, ContextElem.CreateWithAssumptions(assumptions), conclusion, proof);
        }

        private IList<Tuple<TermIdent, TypeIsa>> GlobalFixedVariables()
        {
            var absValType = new VarType("a");
            PureTyIsaTransformer pureTyIsaTransformer = LemmaHelper.ConretePureTyIsaTransformer(absValType);
            
            var result = new List<Tuple<TermIdent, TypeIsa>>
            {
                Tuple.Create((TermIdent) boogieContext.absValTyMap, IsaBoogieType.AbstractValueTyFunType(absValType)),
                Tuple.Create((TermIdent) boogieContext.varContext, IsaBoogieType.VarContextType()),
                Tuple.Create((TermIdent) boogieContext.funContext, IsaBoogieType.FunInterpType(absValType)),
                Tuple.Create(normalInitState, IsaBoogieType.NormalStateType(absValType))
            };

            foreach (KeyValuePair<Function, TermIdent> kv in funToInterpMapping)
            {
                result.Add(Tuple.Create(kv.Value, IsaBoogieType.BoogieFuncInterpType(absValType)));
            }

            foreach (Function boogieFun in methodData.Functions)
            {
                //get untyped version, maybe should precompute this somewhere and re-use or get the data from the VC
                TypeUtil.SplitTypeParams(boogieFun.TypeParameters, boogieFun.InParams.Select(v => v.TypedIdent.Type),
                    out List<TypeVariable> explicitTypeVars, out _);

                TypeIsa typeIsa = pureTyIsaTransformer.Translate(new Function(null, boogieFun.Name,
                    explicitTypeVars, boogieFun.InParams, boogieFun.OutParams[0]));
                result.Add(Tuple.Create(IsaCommonTerms.TermIdentFromName(uniqueNamer.GetName(boogieFun, boogieFun.Name)), typeIsa));
            }

            foreach (Variable v in programVariables)
            {
                TypeIsa typeIsa = pureTyIsaTransformer.Translate(v);
                result.Add(Tuple.Create(IsaCommonTerms.TermIdentFromName(uniqueNamer.GetName(v, v.Name)), typeIsa));
            }

            return result;
        }

        public ContextElem Context()
        {
            return new ContextElem(
                GlobalFixedVariables(), 
                assmManager.AllAssumptions(funToInterpMapping, declToVCMapping, normalInitState, boogieContext, variableFactory.CreateTranslation().VarTranslation), 
                assmManager.AllAssumptionLabels()
                );
        }

        public IList<OuterDecl> Prelude()
        {
            IList<string> assmLabels = assmManager.AllAssumptionLabels();
            var globalAssmsLemmas = new LemmasDecl(globalAssmsName, assmLabels);

            string closedAssm = assmManager.GetAssumptionLabel(AssumptionManager.SpecialAssumptionsKind.TypeValClosed);

            LemmasDecl forallPolyThm = 
                new LemmasDecl("forall_poly_thm", new List<string> {"forall_vc_type[OF " + closedAssm + "]"});
            
            // if One_nat_def is not removed from the simpset, then there is an issue with the assumption "ns 1 = ...",
            // since Isabelle rewrites it to Suc 0 and a subsequent step in the proof may fail
            DeclareDecl decl = new DeclareDecl("Nat.One_nat_def[simp del]");
            
            return new List<OuterDecl>() { globalAssmsLemmas, forallPolyThm, decl };
        }

        private Proof BlockCorrectProof(Block b, string vcHintsName)
        {
            List<string> methods;
            if (vcHintsName == null)
            {
                methods = new List<string>
                {
                    "using assms " + globalAssmsName,
                    "unfolding " + isaBlockInfo.CmdsQualifiedName(b) + "_def",
                    "apply cases",
                    "apply (simp only: " + vcinst.GetVCObjNameRef(b) + "_def)",
                    "apply (handle_cmd_list_full?)",
                    "by (auto?)"
                };
            } else
            {
                methods = new List<string>
                {
                    "using assms ",
                    "unfolding " + isaBlockInfo.CmdsQualifiedName(b) + "_def",
                    "apply (simp only: " + vcinst.GetVCObjNameRef(b) + "_def)",
                    "apply (tactic \\<open> boogie_vc_tac @{context} @{thms " + globalAssmsName + "} " +
                    "@{thm forall_poly_thm} " + vcHintsName + " \\<close>)",
                    "by (auto?)"
                };
            }

            return new Proof(methods);
        }

        private static Term ConclusionBlock(Block b,
            IEnumerable<Block> b_successors,
            Term normalInitState,
            Term finalState,
            IDictionary<NamedDeclaration, Term> declToVCMapping,
            VCInstantiation<Block> vcinst,
            bool useMagicFinalState = false)
        {
            if (useMagicFinalState)
            {
                return new TermBinary(finalState, IsaBoogieTerm.Magic(), TermBinary.BinaryOpCode.EQ);
            }

            Term nonFailureConclusion = new TermBinary(finalState, IsaBoogieTerm.Failure(), TermBinary.BinaryOpCode.NEQ);

            TermIdent normalFinalState = IsaCommonTerms.TermIdentFromName("n_s'");

            Term ifNormalConclusionLhs = new TermBinary(finalState, IsaBoogieTerm.Normal(normalFinalState), TermBinary.BinaryOpCode.EQ);

            Term ifNormalConclusionRhs1 = new TermBinary(normalFinalState, normalInitState, TermBinary.BinaryOpCode.EQ);

            Term ifNormalConclusionRhs =
                !b_successors.Any() ?
                ifNormalConclusionRhs1 :
                new TermBinary(
                    ifNormalConclusionRhs1,
                    LemmaHelper.ConjunctionOfSuccessorBlocks(b_successors, declToVCMapping, vcinst),
                    TermBinary.BinaryOpCode.AND);

            Term ifNormalConclusion =
                new TermQuantifier(
                    TermQuantifier.QuantifierKind.ALL,
                    new List<Identifier>() { normalFinalState.id },
                    new TermBinary(
                        ifNormalConclusionLhs,
                        ifNormalConclusionRhs,
                        TermBinary.BinaryOpCode.IMPLIES)
                    );

            return new TermBinary(nonFailureConclusion, ifNormalConclusion, TermBinary.BinaryOpCode.AND);
        }

        public LemmaDecl MethodVerifiesLemma(CFGRepr cfg, Term methodCfg, string lemmaName)
        {
            Term initConfig = IsaBoogieTerm.CFGConfigNode(new NatConst(cfg.GetUniqueIntLabel(cfg.entry)), IsaBoogieTerm.Normal(normalInitState));
            Term finalNodeOrDone = IsaCommonTerms.TermIdentFromName(uniqueNamer.GetName(new object(), "m'"));

            Term finalConfig = IsaBoogieTerm.CFGConfig(finalNodeOrDone, finalState);

            Term redCfgMulti = IsaBoogieTerm.RedCFGMulti(boogieContext, methodCfg, initConfig, finalConfig);

            List<Term> assumptions = new List<Term>() { redCfgMulti };
            assumptions.Add(vcinst.GetVCObjInstantiation(cfg.entry, declToVCMapping));

            Term conclusion = new TermBinary(finalState, IsaBoogieTerm.Failure(), TermBinary.BinaryOpCode.NEQ);

            //TODO add full proof
            Proof proof = new Proof(new List<string> { "sorry" });

            return new LemmaDecl(lemmaName, ContextElem.CreateWithAssumptions(assumptions), conclusion, proof);
        }
    }   
}
