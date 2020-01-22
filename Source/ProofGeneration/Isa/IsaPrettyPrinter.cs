using System;

using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace ProofGeneration
{

    public class IsaPrettyPrinter
    {
        public static string PrintTheory(Theory thy)
        {
            var sb = new StringBuilder();

            sb.Append("theory ").Append(thy.theoryName);
            sb.AppendLine().Append("imports ").Append(PrettyPrinterHelper.SpaceAggregate(thy.importTheories));
            sb.AppendLine().Append("begin");
            sb.AppendLine();

            var termPrinter = new TermPrettyPrinter();
            var typeIsaPrinter = new TypeIsaPrettyPrinter();
            var outerDeclPrinter = new OuterDeclPrettyPrinter(sb, termPrinter, typeIsaPrinter);

            foreach (OuterDecl outerDecl in thy.decls)
            {
                outerDeclPrinter.Visit(outerDecl);
                sb.AppendLine();
            }

            sb.AppendLine().Append("end");

            return sb.ToString();
        }
    }

    public class OuterDeclPrettyPrinter : OuterDeclVisitor<int>
    {
        StringBuilder _sb
        {
            get;
        }

        TermPrettyPrinter _termPrinter
        {
            get;
        }

        TypeIsaPrettyPrinter _typeIsaPrinter
        {
            get;
        }

        public OuterDeclPrettyPrinter(StringBuilder sb, TermPrettyPrinter termPrinter, TypeIsaPrettyPrinter typeIsaPrinter)
        {
            _sb = sb;
            _termPrinter = termPrinter;
            _typeIsaPrinter = typeIsaPrinter;
        }

        public override int VisitDefDecl(DefDecl d)
        {
            _sb.AppendLine();
            _sb.Append("definition ").Append(d.name);
            _sb.AppendLine().Append(PrettyPrinterHelper.Indent(1)).Append("where");
            _sb.AppendLine().Append(PrettyPrinterHelper.Indent(2));

            string args = PrettyPrinterHelper.SpaceAggregate(_termPrinter.VisitList(d.equation.Item1));

            _sb.Append("\"");
            _sb.Append(d.name).Append(" ").Append(args).Append(" = ").Append(_termPrinter.Visit(d.equation.Item2));
            _sb.Append("\"");

            return 0;
        }

        public override int VisitFunDecl(FunDecl d)
        {
            _sb.AppendLine();
            _sb.Append("fun ").Append(d.name);
            _sb.AppendLine().Append(PrettyPrinterHelper.Indent(1)).Append("where");

            bool first = true;
            foreach (var tuple in d.equations)
            {
                _sb.AppendLine().Append(PrettyPrinterHelper.Indent(2));

                if (first)
                {
                    first = !first;
                }
                else
                {
                    _sb.Append("|");
                }

                string args = PrettyPrinterHelper.SpaceAggregate(_termPrinter.VisitList(tuple.Item1));

                _sb.Append("\"");
                _sb.Append(d.name).Append(" ").Append(args).Append(" = ").Append(_termPrinter.Visit(tuple.Item2));
                _sb.Append("\"");
            }
            return 0;
        }

        
    }


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
            for(int i = t.n; i > 0; i--)
            {
                sb.Append("Suc(");
            }

            sb.Append(0);

            for(int i = 1; i <= t.n; i++)
            {
                sb.Append(")");
            }

            return PrettyPrinterHelper.Parenthesis(sb.ToString());
        }

        public override string VisitIntConst(IntConst t)
        {
            return t.i.ToString();
        }

        public override string VisitStringConst(StringConst t)
        {
            return "''"+t.s+"''";
        }

        public override string VisitTermApp(TermApp t)
        {
            string rFun = Visit(t.fun);
            IList<string> rArgs = VisitList(t.arg);

            return PrettyPrinterHelper.Parenthesis(rFun + " " + PrettyPrinterHelper.SpaceAggregate(rArgs));
        }

        public override string VisitTermIdent(TermIdent t)
        {
            switch(t.id)
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
           return PrettyPrinterHelper.Brackets(PrettyPrinterHelper.CommaAggregate(rArgs));
        }

        public override string VisitTermRecord(TermRecord t)
        {
            var res = t.mapping.Select(tuple => tuple.Item1 + " = " + Visit(tuple.Item2));
            return "(|" + (PrettyPrinterHelper.CommaAggregate(res.ToList())) + "|)";
        }

        public override string VisitTermSet(TermSet t)
        {
            var rArgs = t.elements.Select(tElem => Visit(tElem)).ToList();
            return PrettyPrinterHelper.CurlyBrackets(PrettyPrinterHelper.CommaAggregate(rArgs));
        }

        public override string VisitTermTuple(TermTuple t)
        {
            var res = VisitList(t.terms);
            return PrettyPrinterHelper.Parenthesis(PrettyPrinterHelper.CommaAggregate(res));
        }
    }

    public class TypeIsaPrettyPrinter : TypeIsaVisitor<string>
    {
        public override string VisitArrowType(ArrowType t)
        {
            string rArg = Visit(t.argType);
            string rRes = Visit(t.resType);

            return PrettyPrinterHelper.Parenthesis(rArg + " => " + rRes);
        }

        public override string VisitDataType(DataType t)
        {
            IList<string> rArgs = VisitList(t.args);
            return PrettyPrinterHelper.Parenthesis(t.name + " " + PrettyPrinterHelper.SpaceAggregate(rArgs));
        }

        public override string VisitPrimitiveType(PrimitiveType t)
        {
            switch(t.simpleType)
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
            string aggr = rArgs.Aggregate((s1, s2) => s1 + " " + PrettyPrinterHelper.TIMES + " " + s2);
            return PrettyPrinterHelper.Parenthesis(aggr);
        }

    }

    class PrettyPrinterHelper
    {

        public static readonly string TIMES = "\\<times>";

        public static string Indent(int n)
        {
            //one identation = 2 spaces
            return new string(' ', 2 * n);
        }

        public static string Parenthesis(string s)
        {
            return "(" + s + ")";
        }

        public static string Brackets(string s)
        {
            return "[" + s + "]";
        }

        public static string CurlyBrackets(string s)
        {
            return "{" + s + "}";
        }

        public static string RecordParen(string s)
        {
            return "(|" + s + "|)";
        }

        public static string CommaAggregate(IList<string> list)
        {
            if(list.Count == 0)
            {
                return "";
            } else
            {
                return list.Aggregate((s1, s2) => s1 + ", " + s2);
            }
        }

        public static string SpaceAggregate(IList<string> list)
        {
            if(list.Count == 0)
            {
                return "";
            } else
            {
                return list.Aggregate((s1, s2) => s1 + " " + s2);
            }
        }
    }
}
