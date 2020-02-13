using Microsoft.Boogie;
using ProofGeneration.CFGRepresentation;
using ProofGeneration.Isa;
using System;
using System.Collections.Generic;
using System.Linq;

namespace ProofGeneration.ProgramToVCProof
{
    public class ProgramToVCProof
    {
        public static IList<OuterDecl> GenerateLemmas(Program p, Implementation impl, CFGRepr r)
        {
            BasicCmdIsaVisitor basicCmdVisitor = new BasicCmdIsaVisitor();

            IList<OuterDecl> lemmaDecls = new List<OuterDecl>();

            foreach(Block b in r.GetBlocksBackwards())
            {
                Term context = IsaCommonTerms.TermIdentFromName("\\<Gamma>");
                Term normalInitState = IsaCommonTerms.TermIdentFromName("n_s");
                Term initState = IsaBoogieTerm.Normal(normalInitState);
                Term finalState = IsaCommonTerms.TermIdentFromName("s'");

                Term cmds = new TermList(basicCmdVisitor.Translate(b.Cmds));
                Term cmdsReduce = IsaBoogieTerm.RedCmdList(context, cmds, initState, finalState);

                IDictionary<NamedDeclaration, Term> declToVCMapping = FunAndVariableToVCMapping(p, impl);

                List<Term> assumptions = new List<Term>() { cmdsReduce };
                assumptions.AddRange(VariableAssumptions(impl, normalInitState, declToVCMapping));

                IDictionary<Function, Term> funToInterpMapping = FunctionInterpMapping(p);

                assumptions.AddRange(FunctionAssumptions(p, funToInterpMapping, declToVCMapping));

                //TODO: vc assumption

                Term statement = new TermBinary(finalState, IsaBoogieTerm.Failure(), TermBinary.BinaryOpCode.NEQ);

                Proof oops = new Proof(new List<string>() { "oops" });

                lemmaDecls.Add(new LemmaDecl(b.Label + "_" + "correct", ContextElem.CreateWithAssumptions(assumptions), statement, oops));
            }

            return lemmaDecls;
        }

        public static IDictionary<NamedDeclaration, Term> FunAndVariableToVCMapping(Program p, Implementation impl)
        {
            var dict = new Dictionary<NamedDeclaration, Term>();
            foreach(Function f in p.Functions)
            {
                dict.Add(f, IsaCommonTerms.TermIdentFromName("vc_"+f.Name) );
            }

            foreach(Variable v in impl.InParams.Union(impl.LocVars))
            {
                dict.Add(v, IsaCommonTerms.TermIdentFromName("vc_" + v.Name));
            }

            return dict;
        }

        public static IList<Term> FunctionAssumptions(Program p, 
                IDictionary<Function, Term> funInterpMapping, 
                IDictionary<NamedDeclaration, Term> declToVCMapping
            )
        {
            IList<Term> assumptions = new List<Term>();

            var converter = new PureToBoogieValConverter();

            foreach(Function f in p.Functions)
            {

                //TODO: unique naming scheme
                List<string> boundVars = getNames("farg", f.InParams.Count);

                List<Term> constructedTerms =
                    f.InParams.Select(
                        (v, idx) => converter.ConvertToBoogieVal(v.TypedIdent.Type, IsaCommonTerms.TermIdentFromName(boundVars[idx]))
                   ).ToList();

                Term left = new TermApp(funInterpMapping[f], new List<Term>() { new TermList(constructedTerms) });

                Term right = IsaCommonTerms.SomeOption(
                    new TermApp(declToVCMapping[f], 
                    boundVars.Select(bv => (Term) IsaCommonTerms.TermIdentFromName(bv)).ToList())
                    );

                Term equation = new TermBinary(left, right, TermBinary.BinaryOpCode.EQ);

                assumptions.Add(new TermQuantifier(boundVars, equation, TermQuantifier.QuantifierKind.ALL));
            }

            return assumptions;
        }

        public static List<string> getNames(string baseName, int count)
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

        public static IList<Term> VariableAssumptions(Implementation impl, Term initialState, IDictionary<NamedDeclaration, Term> declToVCMapping)
        {
            var result = new List<Term>();

            var pureToBoogieValConverter = new PureToBoogieValConverter();

            foreach (Variable v in impl.InParams.Union(impl.LocVars))
            {
                Term left = new TermApp(initialState, new List<Term>() { new StringConst(v.Name) });
                Term right = IsaCommonTerms.SomeOption(pureToBoogieValConverter.ConvertToBoogieVal(v.TypedIdent.Type, declToVCMapping[v]));
                result.Add(new TermBinary(left, right, TermBinary.BinaryOpCode.EQ));
            }

            return result;
        }
   
    }
}
