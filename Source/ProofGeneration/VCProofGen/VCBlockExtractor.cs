using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;
using ProofGeneration.CFGRepresentation;
using System;
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
                bool predictionSuccess = PredictBlockName(binding.V.Name, out string predictedBlockName);
                if (predictionSuccess)
                {
                    try
                    {
                        var blockKV = cfg.outgoingBlocks.Single(kv => kv.Key.Label.Equals(predictedBlockName));
                        blockToVC.Add(blockKV.Key, binding.E);
                    } catch(Exception e)
                    {
                        throw new ProofGenUnexpectedStateException<VCBlockExtractor>(typeof(VCBlockExtractor), e.Message);
                    }                   
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

        public static bool PredictBlockName(string vcName, out string predictedBlockName)
        {
            string[] split = vcName.Split(new char[] { '_' });
            if (split.Count() >= 2 && split[split.Length - 1].Equals("correct"))
            {
                predictedBlockName = split.Take(split.Length - 1).Concat("_");
                return true;
            } else
            {
                predictedBlockName = null;
                return false;
            }
        }

    }
}
