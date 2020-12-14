using ProofGeneration.IsaPrettyPrint;

namespace ProofGeneration.Util
{
    public static class ProofUtil
    {

        public static string DefLemma(string defName)
        {
            return defName + "_def";
        }
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

        public static string Apply(string s)
        {
            return "apply (" + s + ")";
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
            return "apply (tactic \\<open> " + tactic + " " + subgoal + "\\<close>)";
        }

        public static string TryRepeatConjI()
        {
            return "tryRepeatConjI";
        }
    }
}
