using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Boogie.GraphUtil;

namespace ProofGeneration.CfgToDag
{
    public class CfgToDagHintManager
    {

        private readonly IDictionary<Block, LoopHeadHint> loopHeadHints = new Dictionary<Block, LoopHeadHint>();

        private readonly IDictionary<Block, List<Block>> backedgeNodeToLoopHead = new Dictionary<Block, List<Block>>();

        private readonly IDictionary<Block, Block> dagToOrig;

        public CfgToDagHintManager(Graph<Block> graph, IDictionary<Block,Block> dagToOrig)
        {
            this.dagToOrig = dagToOrig;
            var origToDag = dagToOrig.ToDictionary(x => x.Value, x => x.Key);
            
            foreach (var loopHead in graph.Headers)
            {
                foreach (var block in graph.BackEdgeNodes(loopHead))
                {
                    if (backedgeNodeToLoopHead.TryGetValue(origToDag[block], out List<Block> loopHeads))
                    {
                       loopHeads.Add(origToDag[loopHead]); 
                    }
                    else
                    {
                        backedgeNodeToLoopHead.Add(origToDag[block], new List<Block> { origToDag[loopHead] });
                    }
                }
            }
        }

        public bool TryIsBackedgeNode(Block block, out List<Block> loopHeadBlock)
        {
            return backedgeNodeToLoopHead.TryGetValue(block, out loopHeadBlock);
        }

        public void AddHint(Block block, LoopHeadHint hint)
        {
            loopHeadHints.Add(block, hint);
        }

        public bool IsLoopHead(Block block, out LoopHeadHint hint)
        {
            return loopHeadHints.TryGetValue(dagToOrig[block], out hint);
        }
        
        public LoopHeadHint GetLoopHead(Block block)
        {
            return loopHeadHints[dagToOrig[block]];
        }
    }
}