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
        public static string Simp(params string [] theorems)
        {
            if(theorems.Length == 0)
            {
                return "simp";
            } else
            {
                return "(simp add:" + IsaPrettyPrinterHelper.SpaceAggregate(theorems) + ")";
            }
        }

        public static string SimpOnly(params string[] theorems)
        {
            if (theorems.Length == 0)
            {
                return "simp";
            }
            else
            {
                return "(simp only:" + IsaPrettyPrinterHelper.SpaceAggregate(theorems) + ")";
            }
        }
    }
}
