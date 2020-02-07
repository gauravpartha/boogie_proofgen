using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace ProofGeneration.IsaPrettyPrint
{
    public class TermPrettyPrinter : TermVisitor<string>
    {
        public override string VisitBoolConst(BoolConst t)
        {
            return t.b ? "True" : "False";
        }

        public override string VisitNatConst(NatConst t)
        {
            //TODO make this configurable (i.e. not necessarily Suc form)

            StringBuilder sb = new StringBuilder("");
            for (int i = t.n; i > 0; i--)
            {
                sb.Append("Suc(");
            }

            sb.Append(0);

            for (int i = 1; i <= t.n; i++)
            {
                sb.Append(")");
            }

            return IsaPrettyPrinterHelper.Parenthesis(sb.ToString());
        }

        public override string VisitIntConst(IntConst t)
        {
            return t.i.ToString();
        }

        public override string VisitStringConst(StringConst t)
        {
            return "''" + t.s + "''";
        }

        public override string VisitTermApp(TermApp t)
        {
            string rFun = Visit(t.fun);
            IList<string> rArgs = VisitList(t.arg);

            return IsaPrettyPrinterHelper.Parenthesis(rFun + " " + IsaPrettyPrinterHelper.SpaceAggregate(rArgs));
        }

        public override string VisitTermIdent(TermIdent t)
        {
            switch (t.id)
            {
                case SimpleIdentifier id:
                    return id.name;
                case Wildcard w:
                    return "_";
                default:
                    throw new NotImplementedException();
            }
        }

        public override string VisitTermList(TermList t)
        {
            var rArgs = VisitList(t.list);
            return IsaPrettyPrinterHelper.Brackets(IsaPrettyPrinterHelper.CommaAggregate(rArgs));
        }

        public override string VisitTermRecord(TermRecord t)
        {
            var res = t.mapping.Select(tuple => tuple.Item1 + " = " + Visit(tuple.Item2));
            return "(|" + (IsaPrettyPrinterHelper.CommaAggregate(res.ToList())) + "|)";
        }

        public override string VisitTermSet(TermSet t)
        {
            var rArgs = t.elements.Select(tElem => Visit(tElem)).ToList();
            return IsaPrettyPrinterHelper.CurlyBrackets(IsaPrettyPrinterHelper.CommaAggregate(rArgs));
        }

        public override string VisitTermTuple(TermTuple t)
        {
            var res = VisitList(t.terms);
            return IsaPrettyPrinterHelper.Parenthesis(IsaPrettyPrinterHelper.CommaAggregate(res));
        }

        public override string VisitTermNAry(TermNAry t)
        {
            throw new NotImplementedException();
        }
    }
}
