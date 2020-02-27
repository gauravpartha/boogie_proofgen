

using Microsoft.Boogie;
using System;
using System.Collections;
using System.Diagnostics.Contracts;
using System.Collections.Generic;
using System.Linq;

namespace ProofGeneration.CFGRepresentation
{
    public class CFGRepr
    {        
        private readonly IDictionary<Block, IList<Block>> outgoingBlocks;
        private readonly IDictionary<Block, int> labeling;
        private readonly Block [] blocks;
        public readonly Block entry;

        //labeling must give topological order from 0 to num_of_blocks-1
        //FIXME: make this more robust
        public CFGRepr(IDictionary<Block, IList<Block>> outgoingBlocks, IDictionary<Block, int> labeling, Block entry)
        {
            Contract.Requires(labeling.Count == labeling.Values.Count && labeling.Values.Count == outgoingBlocks.Count);
            Contract.Requires(labeling.Values.Min() == 0);
            Contract.Requires(labeling.Values.Max() == outgoingBlocks.Count - 1);

            blocks = new Block[outgoingBlocks.Count];

            foreach(var kv in labeling)
            {
                blocks[kv.Value] = kv.Key;
            }

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

        public int GetUniqueIntLabel(Block b)
        {
            return labeling[b];
        }

        public int NumOfBlocks()
        {
            return blocks.Length;
        }

        public IEnumerable<Block> GetBlocksBackwards()
        {
            for (int i = 0; i < blocks.Length; i++)
                yield return blocks[i];
        }

        public IEnumerable<Block> GetBlocksForwards()
        {
            for (int i = blocks.Length - 1; i >= 0; i--)
                yield return blocks[i];
        }

    }
}
