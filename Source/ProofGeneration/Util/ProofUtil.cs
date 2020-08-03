using ProofGeneration.IsaPrettyPrint;

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

        public static string OF(string baseTheorem, params string[] inputTheorems)
        {
            return baseTheorem + "[OF " + IsaPrettyPrinterHelper.SpaceAggregate(inputTheorems) + "]";
        }
    }
}
