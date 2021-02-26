using System;
using System.Linq;
using ProofGeneration.Isa;

namespace ProofGeneration.IsaPrettyPrint
{
    public class TypeIsaPrettyPrinter : TypeIsaVisitor<string>
    {
        public override string VisitVarType(VarType t)
        {
            return IsaPrettyPrinterHelper.Parenthesis("\'" + t.name);
        }

        public override string VisitArrowType(ArrowType t)
        {
            var rArg = Visit(t.argType);
            var rRes = Visit(t.resType);

            return IsaPrettyPrinterHelper.Parenthesis(rArg + " => " + rRes);
        }

        public override string VisitDataType(DataType t)
        {
            var rArgs = VisitList(t.args);
            if (t.args.Count == 0)
                return IsaPrettyPrinterHelper.Parenthesis(t.name);
            return IsaPrettyPrinterHelper.Parenthesis(rArgs.SpaceAggregate() + t.name);
        }

        public override string VisitPrimitiveType(PrimitiveType t)
        {
            switch (t.simpleType)
            {
                case SimpleType.Bool:
                    return "bool";
                case SimpleType.Int:
                    return "int";
                case SimpleType.Nat:
                    return "nat";
                case SimpleType.String:
                    return "string";
                default:
                    throw new NotImplementedException();
            }
        }

        public override string VisitTupleType(TupleType t)
        {
            var rArgs = VisitList(t.args);
            var aggr = rArgs.Aggregate((s1, s2) => s1 + " " + IsaPrettyPrinterHelper.TIMES + " " + s2);
            return IsaPrettyPrinterHelper.Parenthesis(aggr);
        }

        public override string VisitSumType(SumType t)
        {
            var rArgs = VisitList(t.args);
            var aggr = rArgs.Aggregate((s1, s2) => s1 + " + " + s2);
            return IsaPrettyPrinterHelper.Parenthesis(aggr);
        }
    }
}