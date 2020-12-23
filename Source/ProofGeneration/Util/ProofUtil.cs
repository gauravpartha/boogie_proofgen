using System.Collections.Generic;
using ProofGeneration.IsaPrettyPrint;

namespace ProofGeneration.Util
{
    public static class ProofUtil
    {

        public static string DefLemma(string defName)
        {
            return defName + "_def";
        }

        public static string Simp(params string[] theorems)
        {
            return Simp(false, theorems);
        }
        
        public static string SimpAll(params string[] theorems)
        {
            return Simp(true, theorems);
        }
        
        public static string Simp(bool allGoals, string [] theorems)
        {
            string simpTac = "simp" + (allGoals ? "_all" : "");
            if(theorems.Length == 0)
            {
                return simpTac;
            } else
            {
                return "(" + simpTac + " add:" + IsaPrettyPrinterHelper.SpaceAggregate(theorems) + ")";
            }
        }

        public static string SimpAddDel(IEnumerable<string> deleteTheorems, params string[] addTheorems)
        {
            var addString = addTheorems.Length == 0 ? "" : " add: " + IsaPrettyPrinterHelper.SpaceAggregate(addTheorems);
            var delString = addTheorems.Length == 0 ? "" : " del: " + IsaPrettyPrinterHelper.SpaceAggregate(deleteTheorems);

            return "(simp" + addString + delString + ")";
        }


        public static string Apply(string s)
        {
            return "apply (" + s + ")";
        }

        public static string Rule(string s)
        {
            return "rule " + s;
        }
        
        public static string Erule(string s)
        {
            return "erule " + s;
        }
        
        public static string By(string s)
        {
            return "by (" + s + ")";
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

        public static string OF(string baseTheorem, params string[] inputTheorems)
        {
            return baseTheorem + "[OF " + IsaPrettyPrinterHelper.SpaceAggregate(inputTheorems) + "]";
        }

        public static string MLTactic(string tactic, int subgoal)
        {
            return "(tactic \\<open> " + tactic + " " + subgoal + "\\<close>)";
        }

        public static string TryRepeatConjI()
        {
            return "tryRepeatConjI";
        }
    }
}
