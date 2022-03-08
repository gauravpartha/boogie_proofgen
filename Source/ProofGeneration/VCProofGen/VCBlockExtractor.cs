using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;
using ProofGeneration.CFGRepresentation;

namespace ProofGeneration.VCProofGen
{
    internal class VCBlockExtractor
    {
        /// <summary>
        ///     Returns a mapping from blocks to corresponding verification conditions
        ///     Assumes that the expression defines a separate let binding for each block, where the name of the variable is given
        ///     by
        ///     "blockName_correct"
        /// </summary>
        public static IDictionary<Block, VCExpr> BlockToVCMapping(VCExpr vcExpr, CFGRepr cfg)
        {
            var blockToVC = new Dictionary<Block, VCExpr>();

            if (!(vcExpr is VCExprLet))
            {
                if (!vcExpr.Equals(VCExpressionGenerator.True))
                {
                  throw new ProofGenUnexpectedStateException("VC is in unexpected form");
                }
                
                VCExpr trueLit = VCExpressionGenerator.True;
                foreach (Block b in cfg.GetBlocksForwards())
                {
                    blockToVC.Add(b, trueLit);
                }

                return blockToVC;
            }

            var letExpr = vcExpr as VCExprLet;

            foreach (var binding in letExpr)
            {
                var predictionSuccess = PredictBlockName(binding.V.Name, out var predictedBlockName);
                if (predictionSuccess)
                    try
                    {
                        var block = cfg.GetBlocksForwards().Single(b => b.Label.Equals(predictedBlockName));
                        blockToVC.Add(block, binding.E);
                    }
                    catch (Exception e)
                    {
                        throw new ProofGenUnexpectedStateException(typeof(VCBlockExtractor), e.Message);
                    }
                else
                    throw new ProofGenUnexpectedStateException(typeof(VCBlockExtractor),
                        "let binding does not correspond to block");
            }

            if (blockToVC.Count != cfg.NumOfBlocks())
                throw new ProofGenUnexpectedStateException(typeof(VCBlockExtractor),
                    "could not find let binding for all blocks");

            return blockToVC;
        }

        public static bool PredictBlockName(string vcName, out string predictedBlockName)
        {
            var split = vcName.Split(new[] {'_'});
            if (split.Length >= 2 && split[split.Length - 1].Equals("correct"))
            {
                predictedBlockName = split.Take(split.Length - 1).Concat("_");
                return true;
            }

            predictedBlockName = null;
            return false;
        }
    }
}