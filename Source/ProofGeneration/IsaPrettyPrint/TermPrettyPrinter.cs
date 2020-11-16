using ProofGeneration.Isa;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using H = ProofGeneration.IsaPrettyPrint.IsaPrettyPrinterHelper;

namespace ProofGeneration.IsaPrettyPrint
{
    public class TermPrettyPrinter : TermVisitor<string>
    {
        private readonly TypeIsaPrettyPrinter typePrettyPrinter = new TypeIsaPrettyPrinter();

        public override string VisitBoolConst(BoolConst t)
        {
            return t.b ? "True" : "False";
        }

        public override string VisitNatConst(NatConst t)
        {
            if (t.useConstructorRepr)
            {
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
                return H.Parenthesis(sb.ToString());
            }
            else {
                return (t.n).ToString();
            }
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

            return H.Parenthesis(rFun + " " + H.SpaceAggregate(rArgs));
        }

        public override string VisitTermWithExplicitType(TermWithExplicitType t)
        {
            string rTerm = Visit(t.term);
            string rType = typePrettyPrinter.Visit(t.type);

            return H.Parenthesis(rTerm + "::" + rType);
        }

        public override string VisitTermIdent(TermIdent t)
        {
            return GetStringFromIdentifier(t.id);
        }

        public override string VisitTermList(TermList t)
        {
            var rArgs = VisitList(t.list);
            return H.Brackets(H.CommaAggregate(rArgs));
        }

        public override string VisitTermRecord(TermRecord t)
        {
            var res = t.mapping.Select(tuple => tuple.Item1 + " = " + Visit(tuple.Item2));
            return "(|" + (H.CommaAggregate(res.ToList())) + "|)";
        }

        public override string VisitTermSet(TermSet t)
        {
            var rArgs = t.elements.Select(tElem => Visit(tElem)).ToList();
            return H.CurlyBrackets(H.CommaAggregate(rArgs));
        }

        public override string VisitTermTuple(TermTuple t)
        {
            var res = VisitList(t.terms);
            return H.Parenthesis(H.CommaAggregate(res));
        }

        public override string VisitTermQuantifier(TermQuantifier t)
        {
            string qIsa = GetStringFromQuantifier(t.quantifier);
            StringBuilder sb = new StringBuilder();
            sb.Append("(");
            sb.Append(qIsa);
            sb.Append(" ");

            IEnumerable<string> boundVarsTranslated;
            if (t.boundVarTypes != null)
            {
                boundVarsTranslated = t.boundVars.Zip(t.boundVarTypes, (id, ty) =>
                    H.Parenthesis(GetStringFromIdentifier(id) + "::" + typePrettyPrinter.Visit(ty))
                );
            }
            else
            {
                boundVarsTranslated = t.boundVars.Select(GetStringFromIdentifier);
            }

            sb.Append(H.SpaceAggregate(boundVarsTranslated));
            sb.Append(".");

            sb.Append(" ");
            sb.Append(t.term.Dispatch(this));
            sb.Append(")");

            return sb.ToString();
        }

        public override string VisitTermCaseOf(TermCaseOf t)
        {
            StringBuilder sb = new StringBuilder();

            sb.Append("(case ");
            sb.Append(t.termToMatch.Dispatch(this));
            sb.AppendLine(" of ");
            bool first = true;
            foreach (var (item1, item2) in t.matchCases)
            {
                if (!first)
                    sb.Append("|");
                else
                    first = false;
                sb.Append(item1.Dispatch(this));
                sb.Append(" \\<Rightarrow> ");
                sb.AppendLine(item2.Dispatch(this));
            }
            sb.Append(")");

            return sb.ToString();
        }

        public string GetStringFromQuantifier(TermQuantifier.QuantifierKind q)
        {
            switch(q)
            {
                case TermQuantifier.QuantifierKind.ALL:
                    return "\\<forall>";
                case TermQuantifier.QuantifierKind.EX:
                    return "\\<exists>";
                case TermQuantifier.QuantifierKind.META_ALL:
                    return "\\<And>";
                case TermQuantifier.QuantifierKind.LAMBDA:
                    return "\\<lambda>";
                default:
                    throw new NotImplementedException();
            }
        }

        public override string VisitTermBinary(TermBinary t)
        {
            //TODO: for critical operations, use a stack
            string isaSymbol = GetStringFromBinary(t.op);
            string leftString = t.argLeft.Dispatch(this);
            string rightString = t.argRight.Dispatch(this);

            return H.Parenthesis(leftString + " " + isaSymbol + " " + rightString);
        }

        public string GetStringFromIdentifier(Identifier id)
        {
            switch (id)
            {
                case SimpleIdentifier sid:
                    return sid.name;
                case Wildcard w:
                    return "_";
                default:
                    throw new NotImplementedException();
            }
        }

        public string GetStringFromBinary(TermBinary.BinaryOpCode bop)
        {
            switch (bop)
            {
                case TermBinary.BinaryOpCode.META_IMP:
                    return "\\<Longrightarrow>";
                case TermBinary.BinaryOpCode.ADD:
                    return "+";
                case TermBinary.BinaryOpCode.SUB:
                    return "-";
                case TermBinary.BinaryOpCode.MUL:
                    return "*";
                case TermBinary.BinaryOpCode.AND:
                    return "\\<and>";
                case TermBinary.BinaryOpCode.EQ:
                    return "=";
                case TermBinary.BinaryOpCode.NEQ:
                    return "\\<noteq>";
                case TermBinary.BinaryOpCode.IMPLIES:
                    return "\\<longrightarrow>";
                case TermBinary.BinaryOpCode.LT:
                    return "<";
                case TermBinary.BinaryOpCode.LE:
                    return "\\<le>";
                case TermBinary.BinaryOpCode.GT:
                    return ">";
                case TermBinary.BinaryOpCode.GE:
                    return "\\<ge>";
                case TermBinary.BinaryOpCode.OR:
                    return "\\<or>";
                default:
                    throw new NotImplementedException();
            }
        }

        public override string VisitTermUnary(TermUnary t)
        {
            string isaSymbol = GetStringFromUnary(t.op);

            string argString = t.arg.Dispatch(this);

            return H.Parenthesis(isaSymbol + " " + argString);
        }

        public string GetStringFromUnary(TermUnary.UnaryOpCode uop)
        {
            switch(uop)
            {
                case TermUnary.UnaryOpCode.NOT:
                    return "\\<not>";
                default:
                    throw new NotImplementedException();
            }
        }
    }
}
