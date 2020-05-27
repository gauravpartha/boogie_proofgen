using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace ProofGeneration.Util
{
    public static class MLUtil
    {
        public static string DefineVal(string varName, string value)
        {
            return "val " + varName + " = " + value;
        }

        public static string MLList<T>(IEnumerable<T> e)
        {
            var sb = new StringBuilder();
            sb.Append("[");

            bool first = true;

            foreach(var elem in e)
            {
                if(!first)
                {
                    sb.Append(", ");
                } else
                {
                    first = false;
                }
                sb.AppendLine();
                sb.Append(elem.ToString());
            }

            sb.Append("]");

            return sb.ToString();
        }
    }
}
