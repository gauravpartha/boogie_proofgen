using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Isabelle.ML
{
    public static class MLUtil
    {
        public static string DefineVal(string varName, string value)
        {
            return "val " + varName + " = " + value;
        }

        public static string MLList<T>(IEnumerable<T> e) where T : INodeML
        {
            return MLList(e, n => n.GetMLString());
        }

        public static string MLList(IEnumerable<string> e)
        {
            return MLList(e, n => n);
        }

        public static string MLList<T>(IEnumerable<T> e, Func<T, string> stringReprFun)
        {
            var sb = new StringBuilder();
            sb.Append("[");

            var first = true;

            foreach (var elem in e)
            {
                if (!first)
                    sb.Append(", ");
                else
                    first = false;
                sb.AppendLine();
                sb.Append(stringReprFun(elem));
            }

            sb.Append("]");

            return sb.ToString();
        }

        public static string MLTuple(string item1, string item2)
        {
            return "(" + item1 + "," + item2 + ")";
        }

        public static string IsaToMLThm(string isaThm)
        {
            return "@{thm " + isaThm + "}";
        }

        public static string IsaToMLThms(IEnumerable<string> thms)
        {
            if (thms.Any()) return IsaToMLThms(string.Join(" ", thms));

            return "[]";
        }

        public static string IsaToMLThms(string isaThms)
        {
            return "@{thms " + isaThms + "}";
        }

        public static string ContextAntiquotation()
        {
            return "@{context}";
        }
    }
}