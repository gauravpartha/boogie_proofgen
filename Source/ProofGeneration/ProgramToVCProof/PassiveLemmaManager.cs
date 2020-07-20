using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.CFGRepresentation;
using ProofGeneration.Isa;
using ProofGeneration.Util;
using ProofGeneration.VCProofGen;

namespace ProofGeneration.ProgramToVCProof
{
    class PassiveLemmaManager : IBlockLemmaManager
    {
        private readonly VCInstantiation vcinst;
        private readonly IEnumerable<Function> functions;
        private readonly IEnumerable<Variable> programVariables;

        private readonly TermIdent varContext = IsaCommonTerms.TermIdentFromName("\\<Lambda>");
        private readonly TermIdent functionContext = IsaCommonTerms.TermIdentFromName("\\<Gamma>");
        private readonly TermIdent normalInitState = IsaCommonTerms.TermIdentFromName("n_s");
        private readonly Term initState;
        private readonly TermIdent finalState = IsaCommonTerms.TermIdentFromName("s'");

        private readonly IDictionary<NamedDeclaration, TermIdent> declToVCMapping;
        private readonly IDictionary<Function, TermIdent> funToInterpMapping;

        private readonly MultiCmdIsaVisitor cmdIsaVisitor;

        private readonly IsaUniqueNamer uniqueNamer = new IsaUniqueNamer();

        private readonly string globalAssmsName = "global_assms";

        public PassiveLemmaManager(VCInstantiation vcinst, IEnumerable<Function> functions, IEnumerable<Variable> inParams, IEnumerable<Variable> localVars, IEnumerable<Variable> outParams)
        {
            this.vcinst = vcinst;
            this.functions = functions;
            programVariables = inParams.Union(localVars).Union(outParams);
            initState = IsaBoogieTerm.Normal(normalInitState);
            cmdIsaVisitor = new MultiCmdIsaVisitor(uniqueNamer);
            declToVCMapping = LemmaHelper.DeclToTerm(((IEnumerable<NamedDeclaration>)functions).Union(programVariables), uniqueNamer);
            //separate unique namer for function interpretations (since they already have a name in uniqueNamer): possible clashes
            funToInterpMapping = LemmaHelper.FunToTerm(functions, new IsaUniqueNamer());
        }

        public LemmaDecl GenerateBlockLemma(Block block, IEnumerable<Block> successors, string lemmaName, string vcHintsName)
        {
            Term cmds = new TermList(cmdIsaVisitor.Translate(block.Cmds));
            Term cmdsReduce = IsaBoogieTerm.RedCmdList(varContext, functionContext, cmds, initState, finalState);

            List<Term> assumptions = new List<Term>() { cmdsReduce };
            assumptions.Add(vcinst.GetVCBlockInstantiation(block, declToVCMapping));

            Term conclusion = ConclusionBlock(block, successors, normalInitState, finalState, declToVCMapping, vcinst, LemmaHelper.FinalStateIsMagic(block));

            Proof proof = BlockCorrectProof(block, vcHintsName);

            return new LemmaDecl(lemmaName, ContextElem.CreateWithAssumptions(assumptions), conclusion, proof);
        }

        public LemmaDecl GenerateEmptyBlockLemma(Block block, IEnumerable<Block> successors, string lemmaName)
        {
            Term cmds = new TermList(cmdIsaVisitor.Translate(block.Cmds));
            Term cmdsReduce = IsaBoogieTerm.RedCmdList(varContext, functionContext, cmds, initState, finalState);

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
            PureTyIsaTransformer pureTyIsaTransformer = new PureTyIsaTransformer();

            var result = new List<Tuple<TermIdent, TypeIsa>>
            {
                Tuple.Create(varContext, IsaBoogieType.VarContextType()),
                Tuple.Create(functionContext, IsaBoogieType.FunContextType()),
                Tuple.Create(normalInitState, IsaBoogieType.NormalStateType())
            };

            foreach (KeyValuePair<Function, TermIdent> kv in funToInterpMapping)
            {
                result.Add(Tuple.Create(kv.Value, IsaBoogieType.BoogieFuncInterpType()));
            }

            foreach (KeyValuePair<NamedDeclaration, TermIdent> kv in declToVCMapping)
            {
                TypeIsa typeIsa = pureTyIsaTransformer.Translate(kv.Key);
                result.Add(Tuple.Create(kv.Value, typeIsa));
            }

            return result;
        }

        public ContextElem Context()
        {
            return new ContextElem(GlobalFixedVariables(), GlobalAssumptions(), AssumptionLabels());
        }

        public IList<OuterDecl> Prelude()
        {
            IList<string> assmLabels = AssumptionLabels();
            var globalAssmsLemmas = new LemmasDecl(globalAssmsName, assmLabels);

            return new List<OuterDecl>() { globalAssmsLemmas };
        }

        private IList<string> AssumptionLabels()
        {
            return LemmaHelper.AssumptionLabels("G", 0, 2*functions.Count() + programVariables.Count());
        }

        private IList<Term> GlobalAssumptions()
        {
            var results = new List<Term>();
            results.AddRange(GlobalFunctionContextAssumptions());
            results.AddRange(GlobalStateAssumptions());
            return results;
        }

        private IList<Term> GlobalFunctionContextAssumptions()
        {
            return LemmaHelper.FunctionAssumptions(functions, funToInterpMapping, declToVCMapping, functionContext);            
        }

        private IList<Term> GlobalStateAssumptions()
        {
            return LemmaHelper.VariableAssumptions(programVariables, normalInitState, declToVCMapping, uniqueNamer);
        }

        private Proof BlockCorrectProof(Block b, string vcHintsName)
        {
            List<string> methods;
            if (vcHintsName == null)
            {
                methods = new List<string>
                {
                    "using assms " + globalAssmsName,
                    "apply cases",
                    "apply (simp only: " + vcinst.GetVCBlockNameRef(b) + "_def)",
                    "apply (handle_cmd_list_full?)",
                    "by (auto?)"
                };
            } else
            {
                methods = new List<string>
                {
                    "using assms ",
                    "apply (simp only: " + vcinst.GetVCBlockNameRef(b) + "_def)",
                    "apply (tactic \\<open> b_vc_hint_tac_2 @{context} @{thms "+ globalAssmsName + "} " + vcHintsName + " \\<close>)",
                    "by (auto?)"
                };                    
            }

            return new Proof(methods);
        }

        private static Term ConclusionBlock(Block b,
            IEnumerable<Block> b_successors,
            Term normalInitState,
            Term finalState,
            IDictionary<NamedDeclaration, TermIdent> declToVCMapping,
            VCInstantiation vcinst,
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
                b_successors.Count() == 0 ?
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

            Term redCfgMulti = IsaBoogieTerm.RedCFGMulti(varContext, functionContext, methodCfg, initConfig, finalConfig);

            List<Term> assumptions = new List<Term>() { redCfgMulti };
            assumptions.Add(vcinst.GetVCBlockInstantiation(cfg.entry, declToVCMapping));

            Term conclusion = new TermBinary(finalState, IsaBoogieTerm.Failure(), TermBinary.BinaryOpCode.NEQ);

            //TODO add full proof
            Proof proof = new Proof(new List<string> { "sorry" });

            return new LemmaDecl(lemmaName, ContextElem.CreateWithAssumptions(assumptions), conclusion, proof);
        }
    }   
}
