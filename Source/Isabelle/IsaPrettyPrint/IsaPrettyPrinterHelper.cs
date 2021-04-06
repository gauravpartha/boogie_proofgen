using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Isabelle.IsaPrettyPrint
{
    public static class IsaPrettyPrinterHelper
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

        public static string CommaAggregate(IEnumerable<string> list)
        {
            return String.Join(",", list);
        }

        public static string CommaNewLineAggregate(IEnumerable<string> list)
        {
            return String.Join(", " + Environment.NewLine, list);
        }

        public static string SpaceAggregate<T>(this IEnumerable<T> list)
        {
            return String.Join(" ", list);
        }

        public static string Inner(string innerTerm)
        {
            return "\"" + innerTerm + "\"";
        }

        public static void AppendInner(this StringBuilder sb, string s)
        {
            sb.Append("\"");
            sb.Append(s);
            sb.Append("\"");
        }

        public static void AppendInner(this StringBuilder sb, Action action)
        {
            sb.Append("\"");
            action.Invoke();
            sb.Append("\"");
        }
    }
}