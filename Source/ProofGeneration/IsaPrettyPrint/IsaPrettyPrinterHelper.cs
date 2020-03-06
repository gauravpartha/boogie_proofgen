using System;
using System.Collections.Generic;
using System.Linq;

namespace ProofGeneration.IsaPrettyPrint
{
    class IsaPrettyPrinterHelper
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
            if (list.Count == 0)
            {
                return "";
            }
            else
            {
                return list.Aggregate((s1, s2) => s1 + ", " + s2);
            }
        }

        public static string CommaNewLineAggregate(IList<string> list)
        {
            if (list.Count == 0)
            {
                return "";
            }
            else
            {
                return list.Aggregate((s1, s2) => s1 + ", " + Environment.NewLine + s2);
            }
        }

        public static string SpaceAggregate(IList<string> list)
        {
            if (list.Count == 0)
            {
                return "";
            }
            else
            {
                return list.Aggregate((s1, s2) => s1 + " " + s2);
            }
        }
    }
}
