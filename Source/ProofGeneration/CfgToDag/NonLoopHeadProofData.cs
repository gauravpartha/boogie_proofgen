using System;
using Microsoft.Boogie;

namespace ProofGeneration.CfgToDag
{
    public class NonLoopHeadProofData : ICfgToDagProofData
    {
        private readonly string _redCfgAssmName;
        private readonly string _dagAssmName;
        private readonly string _dagVerifiesName;

        private readonly Func<Block, string> _indHypNameFunc;
        
        public NonLoopHeadProofData(
            string redCfgAssmName,
            string dagAssmName,
            string dagVerifiesName,
            Func<Block, string> indHypNameFunc
        )
        {
            _redCfgAssmName = redCfgAssmName;
            _dagAssmName = dagAssmName;
            _dagVerifiesName = dagVerifiesName;
            _indHypNameFunc = indHypNameFunc;
        }
        
        public string RedCfgAssmName()
        {
            return _redCfgAssmName;
        }

        public string DagAssmName()
        {
            return _dagAssmName;
        }

        public string DagVerifiesName()
        {
            return _dagVerifiesName;
        }

        public string LoopIndHypName(Block loopHead)
        {
            return _indHypNameFunc(loopHead);
        }
    }
}