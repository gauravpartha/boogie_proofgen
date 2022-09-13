using System;
using System.Linq;
using Isabelle.Ast;

namespace Isabelle.IsaPrettyPrint
{
    public class TypeIsaPrettyPrinter : TypeIsaVisitor<string>
    {
        public override string VisitVarType(VarType t)
        {
            return IsaPrettyPrinterHelper.Parenthesis("\'" + t.Name);
        }

        public override string VisitArrowType(ArrowType t)
        {
            var rArg = Visit(t.ArgType);
            var rRes = Visit(t.ResType);

            return IsaPrettyPrinterHelper.Parenthesis(rArg + " => " + rRes);
        }

        public override string VisitDataType(DataType t)
        {
            var rArgs = VisitList(t.Args);
            if (t.Args.Count == 0)
                return IsaPrettyPrinterHelper.Parenthesis(t.Name);
            return IsaPrettyPrinterHelper.Parenthesis(rArgs.SpaceAggregate() + t.Name);
        }

        public override string VisitPrimitiveType(PrimitiveType t)
        {
            switch (t.SimpleType)
            {
                case SimpleType.Bool:
                    return "bool";
                case SimpleType.Int:
                    return "int";
                case SimpleType.Nat:
                    return "nat";
                case SimpleType.String:
                    return "string";
                case SimpleType.Real:
                    return "real";
                default:
                    throw new NotImplementedException();
            }
        }

        public override string VisitTupleType(TupleType t)
        {
            var rArgs = VisitList(t.Args);
            var aggr = rArgs.Aggregate((s1, s2) => s1 + " " + IsaPrettyPrinterHelper.TIMES + " " + s2);
            return IsaPrettyPrinterHelper.Parenthesis(aggr);
        }

        public override string VisitSumType(SumType t)
        {
            var rArgs = VisitList(t.Args);
            var aggr = rArgs.Aggregate((s1, s2) => s1 + " + " + s2);
            return IsaPrettyPrinterHelper.Parenthesis(aggr);
        }
    }
}