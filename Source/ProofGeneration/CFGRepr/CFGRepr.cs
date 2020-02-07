using Microsoft.Boogie;
using System.Collections.Generic;

namespace ProofGeneration.CFGRepresentation
{
    class CFGRepr
    {
        public readonly IDictionary<Block, IList<Block>> outgoingBlocks;
        public readonly IDictionary<Block, int> labeling;
        public readonly Block entry;
        

        public CFGRepr(IDictionary<Block, IList<Block>> outgoingBlocks, IDictionary<Block, int> labeling, Block entry)
        {
            this.outgoingBlocks = outgoingBlocks;
            this.labeling = labeling;
            this.entry = entry;
        }

    }
}
