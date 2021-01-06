using Microsoft.Boogie;

namespace ProofGeneration.CfgToDag
{
    interface ICfgToDagProofData
    {
        public string RedCfgAssmName();
        public string DagAssmName();
        public string DagVerifiesName();
        public string LoopIndHypName(Block loopHead);
    }
}