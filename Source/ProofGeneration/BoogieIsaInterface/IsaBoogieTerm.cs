using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using Microsoft.Boogie;
using ProofGeneration.Isa;

namespace ProofGeneration
{
    class IsaBoogieTerm
    {

        public static Term ExprFromVal(Term val)
        {
            return new TermApp(IsaCommonTerms.TermIdentFromName("Val"), new List<Term>() { val });
        }

        public static Term Var(string v)
        {
            Term stringConst = new StringConst(v);
            return new TermApp(IsaCommonTerms.TermIdentFromName("Var"), new List<Term>() { stringConst });
        }

        public static Term IntVal(Microsoft.Basetypes.BigNum num)
        {
            Term intConst = new IntConst(num);
            return new TermApp(IsaCommonTerms.TermIdentFromName("IntV"), new List<Term>() { intConst });
        }

        public static Term BoolVal(bool b)
        {
            Term boolConst = new BoolConst(b);
            return new TermApp(IsaCommonTerms.TermIdentFromName("BoolV"), new List<Term>() { boolConst });
        }

        public static Term Assert(Term arg)
        {
            return new TermApp(IsaCommonTerms.TermIdentFromName("Assert"), new List<Term>() { arg });
        }

        public static Term Assume(Term arg)
        {
            return new TermApp(IsaCommonTerms.TermIdentFromName("Assume"), new List<Term>() { arg });
        }

        public static Term Binop(BinaryOperator.Opcode opcode, Term arg1, Term arg2)
        {
            string bopIsa;

            switch(opcode)
            {
                case BinaryOperator.Opcode.Eq:
                    bopIsa = "Eq";
                    break;
                case BinaryOperator.Opcode.Add:
                    bopIsa = "Add";
                    break;
                case BinaryOperator.Opcode.Le:
                    bopIsa = "Le";
                    break;
                case BinaryOperator.Opcode.And:
                    bopIsa = "And";
                    break;
                default:
                    throw new NotImplementedException();
            }

            var list = new List<Term>() { arg1, IsaCommonTerms.TermIdentFromName(bopIsa), arg2 };
            return new TermApp(IsaCommonTerms.TermIdentFromName("BinOp"), list);
        }

        public static Term FunCall(string fname, IList<Term> args)
        {
            var wrapArgs = new TermList(args);
            var fnameAndArgs = new List<Term>() { new StringConst(fname), wrapArgs };

            return new TermApp(IsaCommonTerms.TermIdentFromName("FunExp"), fnameAndArgs);
        }

        public static Term MethodCFGBody(Term entryNode, Term nodeSet, Term outEdges, Term nodeToBlock)
        {
            var mapping =
                new List<Tuple<string, Term>>()
                {
                    new Tuple<string, Term>("entry", entryNode),
                    new Tuple<string, Term>("nodes", nodeSet),
                    new Tuple<string, Term>("out_edges", outEdges),
                    new Tuple<string, Term>("node_to_block", nodeToBlock)
                };

            return new TermRecord(mapping);
        }

        public static Term Method(string methodName, Term parameters, Term localVars, Term methodCFGBody)
        {
            var elements =
                new List<Term>()
                {
                    new StringConst(methodName),
                    parameters,
                    localVars,
                    methodCFGBody
                };

            return new TermTuple(elements);                            
        }

        public static Term Program(List<Term> fdecls, List<Term> mdecls)
        {
            Term fdeclsTerm = new TermList(fdecls);
            Term mdeclsTerm = new TermList(mdecls);

            return new TermApp(IsaCommonTerms.TermIdentFromName("Program"), new List<Term>() { fdeclsTerm, mdeclsTerm });
        }
    }
}
