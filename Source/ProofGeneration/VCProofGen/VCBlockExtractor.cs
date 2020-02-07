﻿using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;
using ProofGeneration.CFGRepresentation;
using System.Collections.Generic;
using System.Linq;

namespace ProofGeneration.VCProofGen
{
    class VCBlockExtractor
    {

        /// <summary>
        /// Returns a mapping from blocks to corresponding verification conditions
        /// Assumes that the expression defines a separate let binding for each block, where the name of the variable is given by
        /// "blockName_correct"
        /// </summary>
        public static IDictionary<Block, VCExpr> BlockToVCMapping(VCExprLet letExpr, CFGRepr cfg)
        {
            var blockToVC = new Dictionary<Block, VCExpr>();

            foreach (VCExprLetBinding binding in letExpr)
            {
                string[] split = binding.V.Name.Split(new char[] { '_' });
                if (split.Count() == 2 && split[1].Equals("correct"))
                {
                    var blockKV = cfg.outgoingBlocks.Single(kv => kv.Key.Label.Equals(split[0]));
                    blockToVC.Add(blockKV.Key, binding.E);
                } else
                {
                    throw new ProofGenUnexpectedStateException<VCBlockExtractor>(typeof(VCBlockExtractor), "let binding does not correspond to block");
                }
            }

            if (blockToVC.Count != cfg.outgoingBlocks.Count)
            {
                throw new ProofGenUnexpectedStateException<VCBlockExtractor>(typeof(VCBlockExtractor), "could not find let binding for all blocks");
            }

            return blockToVC;
        }


    }
}
