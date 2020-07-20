using ProofGeneration.IsaPrettyPrint;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace ProofGeneration.Util
{
    public static class ProofUtil
    {
        public static string Simp(string thm)
        {
            return Simp(new List<string> { thm });
        }

        public static string Simp(List<string> theorems)
        {
            if(theorems.Count == 0)
            {
                return "simp";
            } else
            {
                return "(simp add:" + IsaPrettyPrinterHelper.SpaceAggregate(theorems) + ")";
            }
        }
    }
}
