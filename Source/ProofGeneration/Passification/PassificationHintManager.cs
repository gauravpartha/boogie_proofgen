using System.Collections.Generic;
using Microsoft.Boogie;

namespace ProofGeneration.Passification
{
    public class PassificationHintManager
    {
        private readonly Dictionary<Block, List<PassificationHint>> blockToHints =
            new Dictionary<Block, List<PassificationHint>>();

        private readonly IDictionary<Block, Block> newToOriginal;

        public PassificationHintManager(IDictionary<Block, Block> newToOriginal)
        {
            this.newToOriginal = newToOriginal;
        }

        //hints are added w.r.t. original CFG
        public void AddHint(Block block, Cmd cmd, Variable origVar, Expr passiveExpr)
        {
            if (!blockToHints.TryGetValue(block, out var blockHints))
            {
                blockHints = new List<PassificationHint>();
                blockToHints.Add(block, blockHints);
            }

            blockHints.Add(new PassificationHint(cmd, origVar, passiveExpr));
        }

        //hints are obtained via copied CFG
        public List<PassificationHint> GetHint(Block block)
        {
            if (blockToHints.TryGetValue(newToOriginal[block], out var hints)) return hints;

            return new List<PassificationHint>();
        }
    }
}