using ProofGeneration.Isa;
using System;
using System.Collections.Generic;
using System.Linq;

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
            string rArg = Visit(t.argType);
            string rRes = Visit(t.resType);

            return IsaPrettyPrinterHelper.Parenthesis(rArg + " => " + rRes);
        }

        public override string VisitDataType(DataType t)
        {
            IList<string> rArgs = VisitList(t.args);
            if (t.args.Count == 0)
                return IsaPrettyPrinterHelper.Parenthesis(t.name);
            else
                return IsaPrettyPrinterHelper.Parenthesis(IsaPrettyPrinterHelper.SpaceAggregate(rArgs) + t.name);
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
            IList<string> rArgs = VisitList(t.args);
            string aggr = rArgs.Aggregate((s1, s2) => s1 + " " + IsaPrettyPrinterHelper.TIMES + " " + s2);
            return IsaPrettyPrinterHelper.Parenthesis(aggr);
        }
    }
}
