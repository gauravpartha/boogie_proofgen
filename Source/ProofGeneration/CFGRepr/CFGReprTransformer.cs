using Microsoft.Boogie;
using Microsoft.Boogie.GraphUtil;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using ProofGeneration.Util;
using System.Reflection;
using System;

namespace ProofGeneration.CFGRepresentation
{
    public static class CFGReprTransformer
    {

        private static readonly MethodInfo CloneMethod = typeof(Object).GetMethod("MemberwiseClone", BindingFlags.NonPublic | BindingFlags.Instance);


        //blocks are not copied
        public static CFGRepr getCFGRepresentation(Implementation impl)
        {
            return getCFGRepresentation(impl, false, out IDictionary<Block, Block> newToOldMapping);
        }

        //if "generateCopy", then blocks will be copied and the mapping from the copied blocks to the original blocks is given by "newToOldBlocks"
        public static CFGRepr getCFGRepresentation(Implementation impl, bool generateCopy, out IDictionary<Block, Block> newToOldBlocks)
        {
            Contract.Requires(impl != null);
            Contract.Ensures((generateCopy && newToOldBlocks != null) || (!generateCopy && newToOldBlocks == null));

            IList<Block> blocksToConvert;

            if(generateCopy)
            {
                blocksToConvert = CopyBlocks(impl.Blocks);

                var newToOldInternal = new Dictionary<Block, Block>();
                blocksToConvert.ZipDo(impl.Blocks, (bNew, bOld) => newToOldInternal.Add(bNew, bOld));
                newToOldBlocks = newToOldInternal;
            } else
            {
                blocksToConvert = impl.Blocks;
                newToOldBlocks = null;
            }                

            AlternateCFGRepr(blocksToConvert, out Block entryBlock, out IDictionary < Block, IList < Block >> outgoingBlocks);
            IDictionary<Block, int> labeling = GetTopologicalLabeling(blocksToConvert);
 
            return new CFGRepr(outgoingBlocks, labeling, entryBlock);
        }

        private static void AlternateCFGRepr(IList<Block> blocks, out Block entryBlock, out IDictionary<Block, IList<Block>> outgoingBlocks)
        {
            entryBlock = null;
            int blockNum = 0;
            outgoingBlocks = new Dictionary<Block, IList<Block>>();

            foreach (var block in blocks)
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

        private static IDictionary<Block, int> GetTopologicalLabeling(IList<Block> blocks)
        {
            Contract.Requires(blocks != null);
            Contract.Ensures(blocks.Count == Contract.Result<IDictionary<Block, int>>().Count);
            Contract.Ensures(Contract.Result<IDictionary<Block, int>>().Values.Min() == 0 && 
                             Contract.Result<IDictionary<Block, int>>().Values.Max() == blocks.Count-1);

            //adusted code from VC.cs
            Graph<Block> dag = new Graph<Block>();
            dag.AddSource(blocks[0]);
            foreach (Block b in blocks)
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
                curLabel++;
            }

            return retLabels;
        }

        private static IList<Block> CopyBlocks(IList<Block> blocks)
        {
            //shallow copy of each block + update edges to copied blocks
            //TODO:  need to make sure this is sufficient
            IDictionary<Block, Block> oldToNewBlock = new Dictionary<Block, Block>();

            IList<Block> copyBlocks = new List<Block>();

            foreach (Block b in blocks)
            {
                Block copyBlock = (Block)CloneMethod.Invoke(b, null);
                copyBlocks.Add(copyBlock);
                oldToNewBlock.Add(b, copyBlock);
            }

            //make sure block references are updated accordingly
            foreach (Block copyBlock in copyBlocks)
            {
                if (copyBlock.TransferCmd is GotoCmd gtc)
                {
                    var newSuccessors = gtc.labelTargets.Select(succ => oldToNewBlock[succ]).ToList();
                    GotoCmd gotoCmdCopy = (GotoCmd)CloneMethod.Invoke(gtc, null);
                    gotoCmdCopy.labelTargets = newSuccessors;
                    copyBlock.TransferCmd = gotoCmdCopy;
                } else
                {
                    copyBlock.TransferCmd = (TransferCmd)CloneMethod.Invoke(copyBlock.TransferCmd, null);                    
                }

                if (copyBlock.Predecessors != null)
                {
                    copyBlock.Predecessors = copyBlock.Predecessors.Select(succ => oldToNewBlock[succ]).ToList();                    
                }
            }

            return copyBlocks;
        }      

    }
}
