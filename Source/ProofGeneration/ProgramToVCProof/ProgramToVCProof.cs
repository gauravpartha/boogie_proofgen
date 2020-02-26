using Microsoft.Boogie;
using ProofGeneration.CFGRepresentation;
using ProofGeneration.Isa;
using ProofGeneration.VCProofGen;
using System;
using System.Collections.Generic;
using System.Linq;

namespace ProofGeneration.ProgramToVCProof
{
    public class ProgramToVCProof
    {
        public static IList<OuterDecl> GenerateLemmas(Program p, Implementation impl, CFGRepr cfg, VCInstantiation vcinst)
        {
            var uniqueNamer = new Microsoft.Boogie.VCExprAST.UniqueNamer();
            uniqueNamer.Spacer = "_";           

            BasicCmdIsaVisitor basicCmdVisitor = new BasicCmdIsaVisitor(uniqueNamer);

            IList<OuterDecl> lemmaDecls = new List<OuterDecl>();

            foreach(Block b in cfg.GetBlocksBackwards())
            {
                Term context = IsaCommonTerms.TermIdentFromName("\\<Gamma>");
                Term normalInitState = IsaCommonTerms.TermIdentFromName("n_s");
                Term initState = IsaBoogieTerm.Normal(normalInitState);
                Term finalState = IsaCommonTerms.TermIdentFromName("s'");

                Term cmds = new TermList(basicCmdVisitor.Translate(b.Cmds));
                Term cmdsReduce = IsaBoogieTerm.RedCmdList(context, cmds, initState, finalState);

                //separate unique namer for raw VC values
                IDictionary<NamedDeclaration, Term> declToVCMapping = FunAndVariableToVCMapping(p, impl, new Microsoft.Boogie.VCExprAST.UniqueNamer());

                List<Term> assumptions = new List<Term>() { cmdsReduce };
                assumptions.AddRange(VariableAssumptions(impl, normalInitState, declToVCMapping, uniqueNamer));

                IDictionary<Function, Term> funToInterpMapping = FunctionInterpMapping(p);

                assumptions.AddRange(FunctionAssumptions(p, funToInterpMapping, declToVCMapping, context));
                assumptions.Add(vcinst.GetVCBlockInstantiation(b, declToVCMapping));

                Term conclusion = ConclusionBlock(b, cfg.outgoingBlocks[b], normalInitState, finalState, declToVCMapping, vcinst);

                Proof proof = BlockCorrectProof(b, vcinst);

                lemmaDecls.Add(new LemmaDecl(b.Label + "_" + "correct", ContextElem.CreateWithAssumptions(assumptions), conclusion, proof));
            }

            return lemmaDecls;
        }

        public static Proof BlockCorrectProof(Block b, VCInstantiation vcinst)
        {
            List<string> methods = new List<string>
            {
                "using assms",
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
            IDictionary<NamedDeclaration, Term> declToVCMapping,
            VCInstantiation vcinst)
        {
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
                    b_successors.
                        Select(b_suc => vcinst.GetVCBlockInstantiation(b_suc, declToVCMapping)).
                        Aggregate((vc1, vc2) => new TermBinary(vc1, vc2, TermBinary.BinaryOpCode.AND)),
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

        public static IDictionary<NamedDeclaration, Term> FunAndVariableToVCMapping(Program p, Implementation impl, Microsoft.Boogie.VCExprAST.UniqueNamer vcNamer)
        {
            var dict = new Dictionary<NamedDeclaration, Term>();
            foreach(Function f in p.Functions)
            {
                dict.Add(f, IsaCommonTerms.TermIdentFromName("vc_"+f.Name) );
            }

            foreach(Variable v in impl.InParams.Union(impl.LocVars))
            {
                dict.Add(v, IsaCommonTerms.TermIdentFromName(vcNamer.GetName(v, "vc_" + v.Name)));
            }

            return dict;
        }

        public static IList<Term> FunctionAssumptions(Program p,                
                IDictionary<Function, Term> funInterpMapping, 
                IDictionary<NamedDeclaration, Term> declToVCMapping,
                Term context
            )
        {
            IList<Term> assumptions = new List<Term>();

            var converter = new PureToBoogieValConverter();

            foreach(Function f in p.Functions)
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
                            boundVars.Select(bv => (Term) IsaCommonTerms.TermIdentFromName(bv)).ToList()
                        )
                    )
                    );

                Term equation = new TermBinary(left, right, TermBinary.BinaryOpCode.EQ);

                assumptions.Add(new TermQuantifier(TermQuantifier.QuantifierKind.ALL, boundVars, equation));
                #endregion
            }

            return assumptions;
        }

        public static List<string> GetNames(string baseName, int count)
        {            
            var result = new List<string>();
            for(int i = 0; i < count; i++)
            {
                result.Add(baseName + i);
            }
            return result;
        }

        public static IDictionary<Function, Term> FunctionInterpMapping(Program p)
        {
            var dict = new Dictionary<Function, Term>();
            foreach(Function f in p.Functions)
            {
                dict.Add(f, IsaCommonTerms.TermIdentFromName("isa_" + f.Name));
            }
            return dict;
        }

        public static IList<Term> VariableAssumptions(Implementation impl, Term initialState, IDictionary<NamedDeclaration, Term> declToVCMapping, Microsoft.Boogie.VCExprAST.UniqueNamer uniqueNamer)
        {
            var result = new List<Term>();

            var pureToBoogieValConverter = new PureToBoogieValConverter();

            foreach (Variable v in impl.InParams.Union(impl.LocVars))
            {
                Term left = new TermApp(initialState, new List<Term>() { new StringConst(uniqueNamer.GetName(v, v.Name)) });
                Term right = IsaCommonTerms.SomeOption(pureToBoogieValConverter.ConvertToBoogieVal(v.TypedIdent.Type, declToVCMapping[v]));
                result.Add(new TermBinary(left, right, TermBinary.BinaryOpCode.EQ));
            }

            return result;
        }
   
    }
}
