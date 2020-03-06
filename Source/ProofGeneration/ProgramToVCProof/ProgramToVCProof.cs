using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.CFGRepresentation;
using ProofGeneration.Isa;
using ProofGeneration.Util;
using ProofGeneration.VCProofGen;
using System;
using System.Collections.Generic;
using System.Linq;

namespace ProofGeneration.ProgramToVCProof
{
    public class PassifiedProgToVCManager
    {
        private readonly TermIdent context = IsaCommonTerms.TermIdentFromName("\\<Gamma>");
        private readonly TermIdent normalInitState = IsaCommonTerms.TermIdentFromName("n_s");
        private readonly Term initState;
        private readonly TermIdent finalState = IsaCommonTerms.TermIdentFromName("s'");



        private readonly VCInstantiation vcinst;
        private readonly IEnumerable<Function> functions;
        private readonly IEnumerable<Variable> inParams;
        private readonly IEnumerable<Variable> localVars;

        private readonly IDictionary<NamedDeclaration, TermIdent> declToVCMapping;
        private readonly IDictionary<Function, TermIdent> funToInterpMapping;

        private readonly MultiCmdIsaVisitor cmdIsaVisitor;        

        private readonly IsaUniqueNamer uniqueNamer = new IsaUniqueNamer();

        public PassifiedProgToVCManager(VCInstantiation vcinst, IEnumerable<Function> functions, IEnumerable<Variable> inParams, IEnumerable<Variable> localVars)
        {
            this.vcinst = vcinst;
            this.functions = functions;
            this.inParams = inParams;
            this.localVars = localVars;
            initState = IsaBoogieTerm.Normal(normalInitState);
            cmdIsaVisitor = new MultiCmdIsaVisitor(uniqueNamer);
            declToVCMapping = FunAndVariableToVCMapping(functions, inParams, localVars, new IsaUniqueNamer());
            funToInterpMapping = FunctionInterpMapping(functions);
        }

        public IList<Term> GetStateAssumptions()
        {
            IList<Term> assumptions = VariableAssumptions(inParams, localVars, normalInitState, declToVCMapping, uniqueNamer);
            foreach(Term assm in FunctionAssumptions(functions, funToInterpMapping, declToVCMapping, context))
            {
                assumptions.Add(assm);
            }

            return assumptions;
        }

        public IList<Tuple<TermIdent, TypeIsa>> GetFixedVariables()
        {

            PureTyIsaTransformer pureTyIsaTransformer = new PureTyIsaTransformer();

            var result = new List<Tuple<TermIdent, TypeIsa>>
            {
                Tuple.Create(normalInitState, IsaBoogieType.NormalStateType())
            };

            foreach (KeyValuePair<Function, TermIdent> kv in funToInterpMapping)
            {
                TypeIsa typeIsa = new ArrowType(IsaCommonTypes.GetListType(IsaBoogieType.ValType()),
                   IsaCommonTypes.GetOptionType(IsaBoogieType.ValType()));
                result.Add(Tuple.Create(kv.Value, typeIsa));
            }

            foreach (KeyValuePair<NamedDeclaration, TermIdent> kv in declToVCMapping)
            {
                TypeIsa typeIsa = pureTyIsaTransformer.TranslateDeclType(kv.Key);
                result.Add(Tuple.Create(kv.Value, typeIsa));
            }

            return result;
        }

        public LemmaDecl GenerateVCBlockLemma(Block block, IEnumerable<Block> successors, string lemmaName)
        {
            Term cmds = new TermList(cmdIsaVisitor.Translate(block.Cmds));
            Term cmdsReduce = IsaBoogieTerm.RedCmdList(context, cmds, initState, finalState);

            List<Term> assumptions = new List<Term>() { cmdsReduce };
            assumptions.Add(vcinst.GetVCBlockInstantiation(block, declToVCMapping));

            bool isTrivialBlock = block.Cmds.Any(cmd =>
            {
                return cmd != null && (cmd is PredicateCmd predCmd && predCmd.Expr is LiteralExpr predCond && (predCond != null && predCond.IsFalse));
            }
            );

            Term conclusion = ConclusionBlock(block, successors, normalInitState, finalState, declToVCMapping, vcinst, isTrivialBlock);

            Proof proof = BlockCorrectProof(block, vcinst);

            return new LemmaDecl(lemmaName, ContextElem.CreateWithAssumptions(assumptions), conclusion, proof);
        }
        
        public LemmaDecl GenerateVCPassiveBlockLemma(Block block, 
            Block origBlock,
            IEnumerable<Block> origSuccessors,
            string lemmaName)
        {
            Term cmds = new TermList(cmdIsaVisitor.Translate(block.Cmds));
            Term cmdsReduce = IsaBoogieTerm.RedCmdList(context, cmds, initState, finalState);

            List<Term> assumptions = new List<Term>() { cmdsReduce };
            assumptions.Add(vcinst.GetVCBlockInstantiation(origBlock, declToVCMapping));

            bool isTrivialBlock = block.Cmds.Any(cmd =>
                {
                    return cmd != null && (cmd is PredicateCmd predCmd && predCmd.Expr is LiteralExpr predCond && (predCond != null && predCond.IsFalse));
                }
            );

            Term conclusion = ConclusionBlock(origBlock, origSuccessors, normalInitState, finalState, declToVCMapping, vcinst, isTrivialBlock);

            return new LemmaDecl(lemmaName, ContextElem.CreateWithAssumptions(assumptions), conclusion, new Proof(new List<string>() { "oops" }));
        }


        public LemmaDecl GenerateEmptyBlockLemma(Block block, ISet<Block> nonEmptySuccessors, string lemmaName)
        {
            Term cmds = new TermList(cmdIsaVisitor.Translate(block.Cmds));
            Term cmdsReduce = IsaBoogieTerm.RedCmdList(context, cmds, initState, finalState);

            List<Term> assumptions = new List<Term>() { cmdsReduce };
            if(nonEmptySuccessors.Any())
                assumptions.Add(ConjunctionOfSuccessorBlocks(nonEmptySuccessors, declToVCMapping, vcinst));

            Term conclusion = ConclusionBlock(block,nonEmptySuccessors, normalInitState, finalState, declToVCMapping, vcinst);

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

        public static Proof BlockCorrectProof(Block b, VCInstantiation vcinst)
        {
            List<string> methods = new List<string>
            {
                "using assms state_assms",
                "apply cases",
                "apply (simp only: " + vcinst.GetVCBlockNameRef(b) + "_def)",
                "apply (handle_cmd_list_full?)",
                "by (auto?)"
            };

            return new Proof(methods);
        }

        public static Term ConclusionBlock(Block b, 
            IEnumerable<Block> b_successors, 
            Term normalInitState, 
            Term finalState, 
            IDictionary<NamedDeclaration, TermIdent> declToVCMapping,
            VCInstantiation vcinst,
            bool useMagicFinalState = false)
        {
            if(useMagicFinalState)
            {
                return new TermBinary(finalState, IsaBoogieTerm.Magic(), TermBinary.BinaryOpCode.EQ);
            }

            Term nonFailureConclusion = new TermBinary(finalState, IsaBoogieTerm.Failure(), TermBinary.BinaryOpCode.NEQ);

            string normalFinalState = "n_s'";
            Term normalFinalStateTerm = IsaCommonTerms.TermIdentFromName(normalFinalState);

            Term ifNormalConclusionLhs = new TermBinary(finalState, IsaBoogieTerm.Normal(normalFinalStateTerm), TermBinary.BinaryOpCode.EQ);

            Term ifNormalConclusionRhs1 = new TermBinary(normalFinalStateTerm, normalInitState, TermBinary.BinaryOpCode.EQ);

            Term ifNormalConclusionRhs = 
                b_successors.Count() == 0 ? 
                ifNormalConclusionRhs1 :
                new TermBinary(
                    ifNormalConclusionRhs1,
                    ConjunctionOfSuccessorBlocks(b_successors, declToVCMapping, vcinst),
                    TermBinary.BinaryOpCode.AND);

            Term ifNormalConclusion =
                new TermQuantifier(
                    TermQuantifier.QuantifierKind.ALL,
                    new List<string>() { normalFinalState },
                    new TermBinary(
                        ifNormalConclusionLhs,
                        ifNormalConclusionRhs,
                        TermBinary.BinaryOpCode.IMPLIES)
                    );

            return new TermBinary(nonFailureConclusion, ifNormalConclusion, TermBinary.BinaryOpCode.AND);        
        }

        public static Term ConjunctionOfSuccessorBlocks(IEnumerable<Block> successorBlocks, IDictionary<NamedDeclaration, TermIdent> declToVCMapping, VCInstantiation vcinst)
        {
            return
            successorBlocks.
                Select(b_suc => vcinst.GetVCBlockInstantiation(b_suc, declToVCMapping)).
                Aggregate((vc1, vc2) => new TermBinary(vc1, vc2, TermBinary.BinaryOpCode.AND));
        }

        public IDictionary<NamedDeclaration, TermIdent> FunAndVariableToVCMapping(
            IEnumerable<Function> functions,
            IEnumerable<Variable> inParams,
            IEnumerable<Variable> localVars,
            IsaUniqueNamer vcNamer)
        {
            var dict = new Dictionary<NamedDeclaration, TermIdent>();
            foreach(Function f in functions)
            {
                dict.Add(f, IsaCommonTerms.TermIdentFromName("vc_"+f.Name) );
            }

            foreach(Variable v in inParams.Union(localVars))
            {
                dict.Add(v, IsaCommonTerms.TermIdentFromName(vcNamer.GetName(v, "vc_" + v.Name)));
            }

            return dict;
        }

        public IDictionary<Function, TermIdent> FunctionInterpMapping(IEnumerable<Function> functions)
        {
            var dict = new Dictionary<Function, TermIdent>();
            foreach(Function f in functions)
            {
                dict.Add(f, IsaCommonTerms.TermIdentFromName("isa_" + f.Name));
            }
            return dict;
        }

        private IList<Term> FunctionAssumptions(
                IEnumerable<Function> functions,
                IDictionary<Function, TermIdent> funInterpMapping,
                IDictionary<NamedDeclaration, TermIdent> declToVCMapping,
                Term context
            )
        {
            IList<Term> assumptions = new List<Term>();

            var converter = new PureToBoogieValConverter();

            foreach (Function f in functions)
            {
                #region context well-formed
                Term ctxWfLeft = new TermApp(IsaCommonTerms.Snd(context), new List<Term>() { new StringConst(f.Name) });
                Term ctxWfRight = IsaCommonTerms.SomeOption(funInterpMapping[f]);

                assumptions.Add(new TermBinary(ctxWfLeft, ctxWfRight, TermBinary.BinaryOpCode.EQ));
                #endregion                

                #region relation interpretation and pure function
                //TODO: unique naming scheme
                List<string> boundVars = GetNames("farg", f.InParams.Count);

                List<Term> constructedTerms =
                    f.InParams.Select(
                        (v, idx) => converter.ConvertToBoogieVal(v.TypedIdent.Type, IsaCommonTerms.TermIdentFromName(boundVars[idx]))
                   ).ToList();

                Term left = new TermApp(funInterpMapping[f], new List<Term>() { new TermList(constructedTerms) });

                Term right = IsaCommonTerms.SomeOption(
                    converter.ConvertToBoogieVal(f.OutParams.First().TypedIdent.Type,
                        new TermApp(declToVCMapping[f],
                            boundVars.Select(bv => (Term)IsaCommonTerms.TermIdentFromName(bv)).ToList()
                        )
                    )
                    );

                Term equation = new TermBinary(left, right, TermBinary.BinaryOpCode.EQ);

                assumptions.Add(new TermQuantifier(TermQuantifier.QuantifierKind.ALL, boundVars, equation));
                #endregion
            }

            return assumptions;
        }

        private IList<Term> VariableAssumptions(
            IEnumerable<Variable> inParams,
            IEnumerable<Variable> localVars,
            Term initialState, 
            IDictionary<NamedDeclaration, TermIdent> declToVCMapping, 
            IsaUniqueNamer uniqueNamer)
        {
            var result = new List<Term>();

            var pureToBoogieValConverter = new PureToBoogieValConverter();

            foreach (Variable v in inParams.Union(localVars))
            {
                Term left = new TermApp(initialState, new List<Term>() { new StringConst(uniqueNamer.GetName(v, v.Name)) });
                Term right = IsaCommonTerms.SomeOption(pureToBoogieValConverter.ConvertToBoogieVal(v.TypedIdent.Type, declToVCMapping[v]));
                result.Add(new TermBinary(left, right, TermBinary.BinaryOpCode.EQ));
            }

            return result;
        }

        private List<string> GetNames(string baseName, int count)
        {
            var result = new List<string>();
            for (int i = 0; i < count; i++)
            {
                result.Add(baseName + i);
            }
            return result;
        }

    }
}
