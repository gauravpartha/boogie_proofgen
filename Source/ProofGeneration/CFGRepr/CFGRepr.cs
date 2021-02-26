using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Boogie;

namespace ProofGeneration.CFGRepresentation
{
    public class CFGRepr
    {
        private readonly Block[] blocks;
        public readonly Block entry;
        private readonly IDictionary<Block, int> labeling;
        private readonly IDictionary<Block, IList<Block>> outgoingBlocks;

        //TODO: make this more robust

        /// <param name="outgoingBlocks">successor relationship</param>
        /// <param name="labeling">
        ///     labeling must give topological order from 0 to num_of_blocks-1, if the CFG is acyclic:
        ///     label(block1) is larger than label(block2) if there is a path from block1 to block2
        /// </param>
        /// <param name="entry">entry block of CFG</param>
        public CFGRepr(IDictionary<Block, IList<Block>> outgoingBlocks, IDictionary<Block, int> labeling, Block entry)
        {
            Contract.Requires(labeling.Count == labeling.Values.Count && labeling.Values.Count == outgoingBlocks.Count);
            Contract.Requires(labeling.Values.Min() == 0);
            Contract.Requires(labeling.Values.Max() == outgoingBlocks.Count - 1);

            blocks = new Block[outgoingBlocks.Count];

            foreach (var kv in labeling) blocks[kv.Value] = kv.Key;

            this.outgoingBlocks = outgoingBlocks;
            this.labeling = labeling;
            this.entry = entry;
        }

        public IEnumerable<Block> GetSuccessorBlocks(Block b)
        {
            return outgoingBlocks[b];
        }

        public int NumOfSuccessors(Block b)
        {
            return outgoingBlocks[b].Count;
        }

        /// <summary>
        ///     Returns a unique integer identifier for the input block and if the CFG is acylic, ensures that
        ///     label(block1) is larger than label(block2) if there is a path from block1 to block2
        /// </summary>
        public int GetUniqueIntLabel(Block b)
        {
            return labeling[b];
        }

        public int NumOfBlocks()
        {
            return blocks.Length;
        }

        public bool ContainsBlock(Block b)
        {
            return outgoingBlocks.ContainsKey(b);
        }

        public IEnumerable<Block> GetBlocksBackwards()
        {
            for (var i = 0; i < blocks.Length; i++)
                yield return blocks[i];
        }

        public IEnumerable<Block> GetBlocksForwards()
        {
            for (var i = blocks.Length - 1; i >= 0; i--)
                yield return blocks[i];
        }
    }
}