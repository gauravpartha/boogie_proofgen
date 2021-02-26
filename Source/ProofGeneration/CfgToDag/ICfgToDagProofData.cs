using Microsoft.Boogie;

namespace ProofGeneration.CfgToDag
{
    internal interface ICfgToDagProofData
    {
        public string RedCfgAssmName();
        public string DagAssmName();
        public string DagVerifiesName();
        public string LoopIndHypName(Block loopHead);
    }
}