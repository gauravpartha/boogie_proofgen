using System.Collections.Generic;
using Microsoft.Boogie;

namespace ProofGeneration.CfgToDag
{
    public class LoopHeadProofData : ICfgToDagProofData
    {
        private readonly string _dagVerifiesName;
        private readonly IList<Block> _loops;

        public LoopHeadProofData(string dagVerifiesName, IList<Block> loops)
        {
            _dagVerifiesName = dagVerifiesName;
            _loops = loops;
        }

        public string RedCfgAssmName()
        {
            return "less(2)";
        }

        public string DagAssmName()
        {
            return "less(3)";
        }

        public string DagVerifiesName()
        {
            return _dagVerifiesName;
        }

        public string LoopIndHypName(Block loopHead)
        {
            var idxLoop = _loops.IndexOf(loopHead);
            if (idxLoop < 0)
                throw new ProofGenUnexpectedStateException("could not find " + loopHead.Label + " in loops list");

            /* first loop induction hypothesis starts after the third assumption
             */
            var idx = 4 + idxLoop;
            return "less(" + idx + ")";
        }
    }
}