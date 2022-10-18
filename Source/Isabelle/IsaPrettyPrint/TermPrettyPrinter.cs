using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Isabelle.Ast;
using H = Isabelle.IsaPrettyPrint.IsaPrettyPrinterHelper;

namespace Isabelle.IsaPrettyPrint
{
    public class TermPrettyPrinter : TermVisitor<string>
    {
        private readonly TypeIsaPrettyPrinter typePrettyPrinter = new TypeIsaPrettyPrinter();

        public override string VisitBoolConst(BoolConst t)
        {
            return t.Val ? "True" : "False";
        }

        public override string VisitNatConst(NatConst t)
        {
            if (t.UseConstructorRepr)
            {
                var sb = new StringBuilder("");
                for (var i = t.Val; i > 0; i--) sb.Append("Suc(");

                sb.Append(0);

                for (var i = 1; i <= t.Val; i++) sb.Append(")");
                return H.Parenthesis(sb.ToString());
            }

            return t.Val.ToString();
        }

        public override string VisitIntConst(IntConst t)
        {
            return t.Val.ToString();
        }

        public override string VisitRealConst(RealConst t)
        {
            if (t.Val.IsNegative)
                return $"-{t.Val.Abs.ToDecimalString()}";
            
            return t.Val.ToDecimalString();
        }

        public override string VisitStringConst(StringConst t)
        {
            return "''" + t.s + "''";
        }

        public override string VisitTermApp(TermApp t)
        {
            var rFun = Visit(t.Fun);
            var rArgs = VisitList(t.Arg);

            return H.Parenthesis(rFun + " " + rArgs.SpaceAggregate());
        }

        public override string VisitTermWithExplicitType(TermWithExplicitType t)
        {
            var rTerm = Visit(t.Term);
            var rType = typePrettyPrinter.Visit(t.Type);

            return H.Parenthesis(rTerm + "::" + rType);
        }

        public override string VisitTermIdent(TermIdent t)
        {
            return GetStringFromIdentifier(t.Id);
        }

        public override string VisitTermList(TermList t)
        {
            var rArgs = VisitList(t.List);
            return H.Brackets(H.CommaAggregate(rArgs));
        }

        public override string VisitTermRecord(TermRecord t)
        {
            var res = t.Mapping.Select(tuple => tuple.Item1 + " = " + Visit(tuple.Item2));
            return "(|" + H.CommaAggregate(res.ToList()) + "|)";
        }

        public override string VisitTermSet(TermSet t)
        {
            var rArgs = t.Elements.Select(Visit).ToList();
            return H.CurlyBrackets(H.CommaAggregate(rArgs));
        }

        public override string VisitTermTuple(TermTuple t)
        {
            var res = VisitList(t.Terms);
            return H.Parenthesis(H.CommaAggregate(res));
        }

        public override string VisitTermQuantifier(TermQuantifier t)
        {
            var qIsa = GetStringFromQuantifier(t.Quantifier);
            var sb = new StringBuilder();
            sb.Append("(");
            sb.Append(qIsa);
            sb.Append(" ");

            IEnumerable<string> boundVarsTranslated;
            if (t.BoundVarTypes != null)
                boundVarsTranslated = t.BoundVars.Zip(t.BoundVarTypes, (id, ty) =>
                    H.Parenthesis(GetStringFromIdentifier(id) + "::" + typePrettyPrinter.Visit(ty))
                );
            else
                boundVarsTranslated = t.BoundVars.Select(GetStringFromIdentifier);

            sb.Append(boundVarsTranslated.SpaceAggregate());
            sb.Append(".");

            sb.Append(" ");
            sb.Append(t.Term.Dispatch(this));
            sb.Append(")");

            return sb.ToString();
        }

        public override string VisitTermCaseOf(TermCaseOf t)
        {
            var sb = new StringBuilder();

            sb.Append("(case ");
            sb.Append(t.TermToMatch.Dispatch(this));
            sb.AppendLine(" of ");
            var first = true;
            foreach (var (item1, item2) in t.MatchCases)
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
            switch (q)
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
            var isaSymbol = GetStringFromBinary(t.Op);
            var leftString = t.ArgLeft.Dispatch(this);
            var rightString = t.ArgRight.Dispatch(this);

            return H.Parenthesis(leftString + " " + isaSymbol + " " + rightString);
        }

        public string GetStringFromIdentifier(Identifier id)
        {
            switch (id)
            {
                case SimpleIdentifier sid:
                    return sid.Name;
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
                case TermBinary.BinaryOpCode.MetaImp:
                    return "\\<Longrightarrow>";
                case TermBinary.BinaryOpCode.Add:
                    return "+";
                case TermBinary.BinaryOpCode.Sub:
                    return "-";
                case TermBinary.BinaryOpCode.Mul:
                    return "*";
                case TermBinary.BinaryOpCode.And:
                    return "\\<and>";
                case TermBinary.BinaryOpCode.Eq:
                    return "=";
                case TermBinary.BinaryOpCode.Neq:
                    return "\\<noteq>";
                case TermBinary.BinaryOpCode.Implies:
                    return "\\<longrightarrow>";
                case TermBinary.BinaryOpCode.Lt:
                    return "<";
                case TermBinary.BinaryOpCode.Le:
                    return "\\<le>";
                case TermBinary.BinaryOpCode.Gt:
                    return ">";
                case TermBinary.BinaryOpCode.Ge:
                    return "\\<ge>";
                case TermBinary.BinaryOpCode.Or:
                    return "\\<or>";
                default:
                    throw new NotImplementedException();
            }
        }

        public override string VisitTermUnary(TermUnary t)
        {
            var isaSymbol = GetStringFromUnary(t.Op);

            var argString = t.Arg.Dispatch(this);

            return H.Parenthesis(isaSymbol + " " + argString);
        }

        public string GetStringFromUnary(TermUnary.UnaryOpCode uop)
        {
            switch (uop)
            {
                case TermUnary.UnaryOpCode.Not:
                    return "\\<not>";
                default:
                    throw new NotImplementedException();
            }
        }
    }
}