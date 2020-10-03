using System;
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

        private readonly IDictionary<NamedDeclaration, Term> declToVCMapping;
        private readonly IDictionary<Function, TermIdent> funToInterpMapping;

        private readonly MultiCmdIsaVisitor cmdIsaVisitor;

        private readonly IsaUniqueNamer uniqueNamer = new IsaUniqueNamer();

        private readonly IVariableTranslationFactory variableFactory;

        private readonly string globalAssmsName = "global_assms";

        private readonly IVCVarFunTranslator vcTranslator;

        public PassiveLemmaManager(VCInstantiation<Block> vcinst, 
            BoogieMethodData methodData, 
            IEnumerable<Function> vcFunctions, 
            IVCVarFunTranslator vcTranslator,
            IVariableTranslationFactory variableFactory)
        {
            this.vcinst = vcinst;
            this.methodData = methodData;
            programVariables = methodData.InParams.Union(methodData.Locals).Union(methodData.OutParams);
            initState = IsaBoogieTerm.Normal(normalInitState);
            this.vcTranslator = vcTranslator;
            this.variableFactory = variableFactory;
            cmdIsaVisitor = new MultiCmdIsaVisitor(uniqueNamer, variableFactory);
            boogieContext = new BoogieContextIsa(
              IsaCommonTerms.TermIdentFromName("A"),
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
        }

        public LemmaDecl GenerateBlockLemma(Block block, IEnumerable<Block> successors, string lemmaName, string vcHintsName)
        {
            Term cmds = new TermList(cmdIsaVisitor.Translate(block.Cmds));
            Term cmdsReduce = IsaBoogieTerm.RedCmdList(boogieContext, cmds, initState, finalState);

            List<Term> assumptions = new List<Term>() { cmdsReduce };
            assumptions.Add(vcinst.GetVCObjInstantiation(block, declToVCMapping));

            Term conclusion = ConclusionBlock(block, successors, normalInitState, finalState, declToVCMapping, vcinst, LemmaHelper.FinalStateIsMagic(block));

            Proof proof = BlockCorrectProof(block, vcHintsName);

            return new LemmaDecl(lemmaName, ContextElem.CreateWithAssumptions(assumptions), conclusion, proof);
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
                Tuple.Create((TermIdent) boogieContext.funContext, IsaBoogieType.FunContextType(absValType)),
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
            return new ContextElem(GlobalFixedVariables(), GlobalAssumptions(), AssumptionLabels());
        }

        public IList<OuterDecl> Prelude()
        {
            /* TODO
            IList<string> assmLabels = AssumptionLabels();
            var globalAssmsLemmas = new LemmasDecl(globalAssmsName, assmLabels);

            return new List<OuterDecl>() { globalAssmsLemmas };
            */
            return new List<OuterDecl>() { };
        }

        private IList<string> AssumptionLabels()
        {
            return LemmaHelper.AssumptionLabels("G", 0, 2*(methodData.Functions).Count() + programVariables.Count());
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
            return LemmaHelper.FunctionAssumptions(methodData.Functions, funToInterpMapping, declToVCMapping, boogieContext);            
        }

        private IList<Term> GlobalStateAssumptions()
        {
            return LemmaHelper.VariableAssumptions(programVariables, normalInitState, declToVCMapping, variableFactory.CreateTranslation().VarTranslation);
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
                    "apply (simp only: " + vcinst.GetVCObjNameRef(b) + "_def)",
                    "apply (handle_cmd_list_full?)",
                    "by (auto?)"
                };
            } else
            {
                methods = new List<string>
                {
                    "using assms ",
                    "apply (simp only: " + vcinst.GetVCObjNameRef(b) + "_def)",
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
