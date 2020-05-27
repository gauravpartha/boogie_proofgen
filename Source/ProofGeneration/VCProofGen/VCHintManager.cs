using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;
using System.Collections.Generic;

namespace ProofGeneration.VCProofGen
{
    public class VCHintManager
    {

        private IDictionary<Block, VCHintBlock> blockTo = new Dictionary<Block, VCHintBlock>();

        public static VCHint AssertConjHint = new AssertSimpleHint(AssertSimpleHint.AssertSimpleType.CONJ);
        public static VCHint AssertNoConjHint = new AssertSimpleHint(AssertSimpleHint.AssertSimpleType.NO_CONJ);
        public static VCHint AssertSubsumptionHint = new AssertSimpleHint(AssertSimpleHint.AssertSimpleType.SUBSUMPTION);

        //hints must be provided in a backwards manner (from last to first command)
        public void NextHintForBlock(VCHint hint, Cmd cmd, Block block, VCExpr cmdBodyExpr, VCExpr resultVC)
        {
            VCHint updatedHint = hint;
            if (cmd is AssumeCmd assumeCmd)
            {
                updatedHint = AssumeStmtHint(assumeCmd, cmdBodyExpr, resultVC);
            }

            if (!blockTo.TryGetValue(block, out VCHintBlock vcHintBlock))
            {
                vcHintBlock = new VCHintBlock(block);
                blockTo.Add(block, vcHintBlock);
            }

            vcHintBlock.AddHint(cmd, updatedHint);
        }

        public bool TryGetHints(Block block, out IEnumerable<VCHint> hints)
        {
            if(blockTo.TryGetValue(block, out VCHintBlock vcHintBlock))
            {
                hints = vcHintBlock.Hints;
                return true;
            } else
            {
                hints = null;
                return false;
            }
        }

        private VCHint AssumeStmtHint(AssumeCmd assumeCmd, VCExpr cmdBodyExpr, VCExpr vc)
        {
            if(vc is VCExprNAry vcNAry && vcNAry.Op == VCExpressionGenerator.ImpliesOp)
            {
                VCExpr vcLeft = vcNAry[0];
                int nestLevel = 0;

                while(vcLeft != cmdBodyExpr && vcLeft is VCExprNAry vcLeftNAry && vcLeftNAry.Op == VCExpressionGenerator.AndOp)
                {
                    vcLeft = vcLeftNAry[0];
                    nestLevel++;
                }

                if(vcLeft == cmdBodyExpr)
                {
                    if(nestLevel == 0)
                    {
                        return new AssumeConjHint(0, 0, 1);
                    }
                    {
                        return new AssumeConjHint(nestLevel, nestLevel, -1);
                    }
                } else
                {
                    throw new ProofGenUnexpectedStateException(GetType(), "cannot find assume expression on left hand side of vc implication");
                }
            } else
            {
                throw new ProofGenUnexpectedStateException(GetType(), "unexpected vc of assume statement at top level");
            }
        }
    }
}
