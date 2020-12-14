using System.Collections.Generic;
using System.Diagnostics.Contracts;
using Microsoft.Boogie;
using Microsoft.Boogie.GraphUtil;

namespace ProofGeneration.Util
{
    public static class GraphUtil
    {
        
        public static Graph<Block> GraphFromBlocks(IList<Block> blocks, bool reverse=false)
        {
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
                        if (reverse)
                        {
                            dag.AddEdge(dest, b);
                        }
                        else
                        {
                            dag.AddEdge(b, dest);
                        }
                    }
                }
            }

            return dag;
        }
    }
}