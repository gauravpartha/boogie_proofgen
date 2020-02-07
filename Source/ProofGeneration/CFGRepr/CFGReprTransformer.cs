using Microsoft.Boogie;
using Microsoft.Boogie.GraphUtil;
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace ProofGeneration.CFGRepresentation
{
    class CFGReprTransformer
    {

        static public CFGRepr getCFGRepresentation(Implementation impl)
        {
            AlternateCFGRepr(impl, out Block entryBlock, out IDictionary < Block, IList < Block >> outgoingBlocks);
            IDictionary<Block, int> labeling = GetTopologicalLabeling(impl);
            return new CFGRepr(outgoingBlocks, labeling, entryBlock);
        }

        static private void AlternateCFGRepr(Implementation impl, out Block entryBlock, out IDictionary<Block, IList<Block>> outgoingBlocks)
        {
            Contract.Ensures(entryBlock != null);

            entryBlock = null;
            int blockNum = 0;
            outgoingBlocks = new Dictionary<Block, IList<Block>>();

            foreach (var block in impl.Blocks)
            {
                if (block.Predecessors.Count == 0)
                {
                    if (entryBlock != null)
                    {
                        throw new IsaCFGGeneratorException(IsaCFGGeneratorException.Reason.CFG_NOT_UNIQUE_ENTRY);
                    }
                    entryBlock = block;
                }
                List<Block> curOutgoing = new List<Block>();

                if (block.TransferCmd is GotoCmd gotoCmd)
                {
                    curOutgoing.AddRange(gotoCmd.labelTargets);
                }

                outgoingBlocks.Add(block, curOutgoing);

                blockNum++;
            }

            if (entryBlock == null)
            {
                throw new IsaCFGGeneratorException(IsaCFGGeneratorException.Reason.CFG_NO_ENTRY);
            }
        }

        static private IDictionary<Block, int> GetTopologicalLabeling(Implementation impl)
        {
            Contract.Ensures(impl.Blocks.Count == Contract.Result<IDictionary<Block, int>>().Count);

            //adusted code from VC.cs
            Graph<Block> dag = new Graph<Block>();
            dag.AddSource(impl.Blocks[0]);
            foreach (Block b in impl.Blocks)
            {
                GotoCmd gtc = b.TransferCmd as GotoCmd;
                if (gtc != null)
                {
                    Contract.Assume(gtc.labelTargets != null);
                    foreach (Block dest in gtc.labelTargets)
                    {
                        Contract.Assert(dest != null);
                        dag.AddEdge(dest, b);
                    }
                }
            }
            IEnumerable<Block> sortedNodes = dag.TopologicalSort();
            Contract.Assert(sortedNodes != null);

            var retLabels = new Dictionary<Block, int>();

            int curLabel = 0;
            foreach(Block block in sortedNodes) {
                retLabels.Add(block, curLabel);
            }

            return retLabels;
        }
    }
}
