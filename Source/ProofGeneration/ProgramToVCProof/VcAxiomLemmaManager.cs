using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.BoogieIsaInterface.VariableTranslation;
using ProofGeneration.Isa;
using ProofGeneration.Util;
using ProofGeneration.VCProofGen;

namespace ProofGeneration.ProgramToVCProof
{
    public class VcAxiomLemmaManager : ILocaleContext
    {
        private readonly AssumptionManager assmManager;

        private readonly BasicCmdIsaVisitor basicCmdIsaVisitor;
        private readonly BoogieContextIsa boogieContext;
        private readonly string globalAssmsName = "global_assms";
        private readonly BoogieMethodData methodData;
        private readonly TermIdent normalInitState = IsaCommonTerms.TermIdentFromName("n_s");

        private readonly IsaUniqueNamer uniqueNamer = new IsaUniqueNamer();
        private readonly IVariableTranslationFactory variableFactory;
        private readonly VCInstantiation<VCExpr> vcAxiomInst;
        private readonly VcRewriteLemmaGen vcRewriteLemmaGen;
        private readonly IDictionary<NamedDeclaration, Term> declToVCMapping;
        private readonly IDictionary<Function, TermIdent> funToInterpMapping;


        public VcAxiomLemmaManager(
            VCInstantiation<VCExpr> vcAxiomInst,
            BoogieMethodData methodData,
            IEnumerable<Function> vcFunctions,
            VcRewriteLemmaGen vcRewriteLemmaGen,
            IVariableTranslationFactory variableFactory)
        {
            this.vcAxiomInst = vcAxiomInst;
            this.methodData = methodData;
            this.vcRewriteLemmaGen = vcRewriteLemmaGen;
            this.variableFactory = variableFactory;
            basicCmdIsaVisitor = new BasicCmdIsaVisitor(variableFactory);
            boogieContext = new BoogieContextIsa(IsaCommonTerms.TermIdentFromName("A"),
                IsaCommonTerms.TermIdentFromName("M"), IsaCommonTerms.TermIdentFromName("\\<Lambda>"),
                IsaCommonTerms.TermIdentFromName("\\<Gamma>"), IsaCommonTerms.TermIdentFromName("\\<Omega>"));
            var typeDeclTranslation = new ConcreteTypeDeclTranslation(boogieContext);
            declToVCMapping =
                LemmaHelper.DeclToTerm(
                    ((IEnumerable<NamedDeclaration>) methodData.Functions).Union(methodData.Constants), vcFunctions,
                    typeDeclTranslation, uniqueNamer);
            //separate unique namer for function interpretations (since they already have a name in uniqueNamer): possible clashes
            funToInterpMapping = LemmaHelper.FunToTerm(methodData.Functions, new IsaUniqueNamer());
            assmManager = new AssumptionManager(methodData.Functions, methodData.Constants, variableFactory);
        }

        public ContextElem Context()
        {
            return new ContextElem(
                ContextHelper.GlobalFixedVariables(boogieContext, methodData.Functions, methodData.Constants,
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

        public LemmaDecl AxiomVcLemma(string lemmaName, Axiom axiom, VCExpr vcAxiom, out IList<OuterDecl> requiredDecls)
        {
            var vc = vcAxiomInst.GetVCObjInstantiation(vcAxiom, declToVCMapping);
            var axiomTerm = basicCmdIsaVisitor.Translate(axiom.Expr);
            requiredDecls = new List<OuterDecl>();

            vcRewriteLemmaGen.RequiredVcRewrite(axiom.Expr, true, out var vcRewriteLemmas);

            VCExprHint exprHint;
            if (vcRewriteLemmas != null && vcRewriteLemmas.Any())
            {
                exprHint = new VCExprHint(vcRewriteLemmas);
                requiredDecls.AddRange(vcRewriteLemmas);
            }
            else
            {
                exprHint = VCExprHint.EmptyExprHint();
            }

            var assumption =
                IsaBoogieTerm.RedExpr(boogieContext, axiomTerm, normalInitState, IsaBoogieTerm.BoolVal(true));
            var statement = vc;

            return
                new LemmaDecl(lemmaName,
                    ContextElem.CreateWithAssumptions(assumption),
                    statement,
                    new Proof(new List<string>
                    {
                        "unfolding " + vcAxiomInst.GetVCObjNameRef(vcAxiom) + "_def",
                        ProofUtil.By(
                            ProofUtil.MLTactic(
                                "prove_axiom_vc_tac @{context} (" + exprHint.GetMLString() + ") " +
                                MLUtil.IsaToMLThm("assms(1)") + " " + MLUtil.IsaToMLThms(globalAssmsName) +
                                " (@{thm forall_poly_thm}, @{thm exists_poly_thm}) []", 1)
                        )
                    })
                );
        }
    }
}