﻿using Microsoft.Boogie;
using Microsoft.Boogie.GraphUtil;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using ProofGeneration.Util;
using System.Reflection;
using System;
using Type = System.Type;

namespace ProofGeneration.CFGRepresentation
{
    public static class CFGReprTransformer
    {

        private static readonly MethodInfo CloneMethod = typeof(Object).GetMethod("MemberwiseClone", BindingFlags.NonPublic | BindingFlags.Instance);


        //blocks are not copied
        public static CFGRepr getCFGRepresentation(Implementation impl)
        {
            return GetCfgRepresentation(impl, false, out IDictionary<Block, Block> newToOldMapping);
        }

        //if "generateCopy", then blocks will be copied and the mapping from the copied blocks to the original blocks is given by "newToOldBlocks"
        public static CFGRepr GetCfgRepresentation(Implementation impl, bool generateCopy, out IDictionary<Block, Block> newToOldBlocks, bool isAcyclic = true)
        {
            Contract.Requires(impl != null);
            Contract.Ensures((generateCopy && newToOldBlocks != null) || (!generateCopy && newToOldBlocks == null));
            var predecessorMap = ComputePredecessors(impl.Blocks);
            IList<Block> blocksToConvert;
            Func<Block, List<Block>> predecessorFunc;

            if(generateCopy)
            {
                blocksToConvert = CopyBlocks(impl.Blocks, predecessorMap);

                var newToOldInternal = new Dictionary<Block, Block>();
                blocksToConvert.ZipDo(impl.Blocks, (bNew, bOld) => newToOldInternal.Add(bNew, bOld));
                newToOldBlocks = newToOldInternal;
                predecessorFunc = b => b.Predecessors;
            } else
            {
                blocksToConvert = impl.Blocks;
                newToOldBlocks = null;
                predecessorFunc = b => predecessorMap[b];
            }                

            AlternateCFGRepr(blocksToConvert, out Block entryBlock, predecessorFunc, out IDictionary<Block, IList<Block >> outgoingBlocks);
            IDictionary<Block, int> labeling;
            if (isAcyclic)
            {
                labeling = GetTopologicalLabeling(blocksToConvert);
            } else
            {
                labeling = new Dictionary<Block, int>();
                int idx = 0;
                foreach(Block b in blocksToConvert)
                {
                    labeling.Add(b, idx);
                    idx++;
                }
            }

            return new CFGRepr(outgoingBlocks, labeling, entryBlock);
        }

        private static void AlternateCFGRepr(
            IList<Block> blocks, 
            out Block entryBlock, 
            Func<Block, List<Block>> predecessorFunc, 
            out IDictionary<Block, IList<Block>> outgoingBlocks)
        {
            entryBlock = null;
            int blockNum = 0;
            outgoingBlocks = new Dictionary<Block, IList<Block>>();

            foreach (var block in blocks)
            {
                if (predecessorFunc(block).Count == 0)
                {
                    if (entryBlock != null)
                    {
                        throw new ProofGenUnexpectedStateException(typeof(CFGReprTransformer), "no unique CFG entry");
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
                throw new ProofGenUnexpectedStateException(typeof(CFGReprTransformer), "no CFG entry");
            }
        }


        /// <summary>
        /// Copy from <see cref="Implementation"/>. We compute predecessors ourselves, since at certain points the
        /// predecessors property for blocks is not in-sync with the CFG (and we do not want to adjust the Boogie
        /// objects)
        /// </summary>
        private static Dictionary<Block, List<Block>>  ComputePredecessors(IEnumerable<Block> blocks)
        { 
            var predecessors = new Dictionary<Block, List<Block>>();
            foreach (Block b in blocks)
            {
                predecessors.Add(b, new List<Block>());
            }

            foreach (Block b in blocks)
            {
                GotoCmd gtc = b.TransferCmd as GotoCmd;
                if (gtc != null)
                {
                    Contract.Assert(gtc.labelTargets != null);
                    foreach (Block /*!*/ dest in gtc.labelTargets)
                    {
                        Contract.Assert(dest != null);
                        predecessors[dest].Add(b);
                    }
                }
            }

            return predecessors;
        }

        private static IDictionary<Block, int> GetTopologicalLabeling(IList<Block> blocks)
        {
            Contract.Requires(blocks != null);
            Contract.Ensures(blocks.Count == Contract.Result<IDictionary<Block, int>>().Count);
            Contract.Ensures(Contract.Result<IDictionary<Block, int>>().Values.Min() == 0 && 
                             Contract.Result<IDictionary<Block, int>>().Values.Max() == blocks.Count-1);

            //adusted code from VC.cs
            Graph<Block> dag = GraphUtil.GraphFromBlocks(blocks, true);
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

        /// <summary>
        /// Makes a shallow copy of <paramref name="blocks"/>. The predecessors of <paramref name="blocks"/> is set
        /// correctly.
        /// </summary>
        private static IList<Block> CopyBlocks(IList<Block> blocks, Dictionary<Block, List<Block>> predecessorMap)
        {
            //shallow copy of each block + update edges to copied blocks
            //TODO:  need to make sure this is sufficient
            IDictionary<Block, Block> oldToNewBlock = new Dictionary<Block, Block>();

            IList<Block> copyBlocks = new List<Block>();

            foreach (Block b in blocks)
            {
                List<Cmd> copyCmds = new List<Cmd>();
                foreach(var cmd in b.Cmds)
                {
                    copyCmds.Add((Cmd) CloneMethod.Invoke(cmd,null));
                }

                Block copyBlock = (Block)CloneMethod.Invoke(b, null);
                copyBlock.Cmds = copyCmds;
                copyBlock.Predecessors = predecessorMap[b];

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
