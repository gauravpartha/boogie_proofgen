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
        public void NextHintForBlock(
            Cmd cmd,
            Block block,
            VCExpr exprVC,
            VCExpr postVC,
            VCExpr resultVC,
            CommandLineOptions.SubsumptionOption subsumption)
        {
            VCHint vcHint;
            if (cmd is AssumeCmd assumeCmd)
            {
                vcHint = AssumeStmtHint(assumeCmd, exprVC, postVC, resultVC);
            } else if (cmd is AssertCmd assertCmd)
            {
                vcHint = AssertStmtHint(assertCmd, exprVC, postVC, subsumption);
            } else
            {
                throw new ProofGenUnexpectedStateException(GetType(), "expected an assert or assume cmd");
            }

            if (!blockTo.TryGetValue(block, out VCHintBlock vcHintBlock))
            {
                vcHintBlock = new VCHintBlock(block);
                blockTo.Add(block, vcHintBlock);
            }

            vcHintBlock.AddHint(cmd, vcHint);
        }

        public bool TryGetHints(Block block, out IEnumerable<VCHint> hints)
        {
            if (blockTo.TryGetValue(block, out VCHintBlock vcHintBlock))
            {
                hints = vcHintBlock.Hints();
                return true;
            }
            else
            {
                hints = null;
                return false;
            }
        }

        private VCHint AssumeStmtHint(AssumeCmd assumeCmd, VCExpr exprVC, VCExpr postVC, VCExpr resultVC)
        {
            if(IsSpecialAssumeStmt(assumeCmd, exprVC, postVC, out VCHint specialHint))
            {
                return specialHint;
            }

            if (resultVC is VCExprNAry vcNAry && vcNAry.Op == VCExpressionGenerator.ImpliesOp)
            {
                VCExpr vcLeft = vcNAry[0];
                int nestLevel = 0;

                while (vcLeft != exprVC && vcLeft is VCExprNAry vcLeftNAry && vcLeftNAry.Op == VCExpressionGenerator.AndOp)
                {
                    vcLeft = vcLeftNAry[0];
                    nestLevel++;
                }

                if (vcLeft == exprVC)
                {
                    if (nestLevel == 0)
                    {
                        return new AssumeConjHint(0, 0, 1);
                    }
                    {
                        return new AssumeConjHint(nestLevel, nestLevel, -1);
                    }
                }
                else
                {
                    throw new ProofGenUnexpectedStateException(GetType(), "cannot find assume expression on left hand side of vc implication");
                }
            }
            else
            {
                throw new ProofGenUnexpectedStateException(GetType(), "unexpected vc of assume statement at top level");
            }
        }

        /// <summary>
        /// check whether assumeCmd is special with respect to VC and if so, store hint in out parameter, otherwise
        /// store null in out parameter
        /// </summary>
        /// <returns>true, if is a special case (out parameter != null), false otherwise</returns>
        private bool IsSpecialAssumeStmt(AssumeCmd assumeCmd, VCExpr exprVC, VCExpr postVC, out VCHint hint)
        {
            if(exprVC.Equals(VCExpressionGenerator.False))
            {
                hint = new AssumeSimpleHint(AssumeSimpleHint.AssumeSimpleType.ASSUME_FALSE);
                return true;
            } else if(postVC.Equals(VCExpressionGenerator.False))
            {
                hint = new AssumeSimpleHint(AssumeSimpleHint.AssumeSimpleType.ASSUME_NOT);
                return true;
            } else if(exprVC.Equals(VCExpressionGenerator.True) || postVC.Equals(VCExpressionGenerator.True))
            {
                hint = new AssumeSimpleHint(AssumeSimpleHint.AssumeSimpleType.ASSUME_TRUE);
                return true;
            }

            hint = null;
            return false;
        }

        private VCHint AssertStmtHint(
            AssertCmd cmd,
            VCExpr exprVC,
            VCExpr postVC,
            CommandLineOptions.SubsumptionOption subsumption)
        {
            if (exprVC.Equals(VCExpressionGenerator.False) || postVC.Equals(VCExpressionGenerator.False))
            {
                return new AssertSimpleHint(AssertSimpleHint.AssertSimpleType.ASSERT_FALSE);
            }
            else if (exprVC.Equals(VCExpressionGenerator.True))
            {
                return new AssertSimpleHint(AssertSimpleHint.AssertSimpleType.ASSERT_TRUE);
            }
            else if (postVC.Equals(VCExpressionGenerator.True))
            {
                return new AssertSimpleHint(AssertSimpleHint.AssertSimpleType.NO_CONJ);
            }
            else if (
              subsumption == CommandLineOptions.SubsumptionOption.Always ||
              (subsumption == CommandLineOptions.SubsumptionOption.NotForQuantifiers && !(exprVC is VCExprQuantifier))
              )
            {
                return new AssertSimpleHint(AssertSimpleHint.AssertSimpleType.SUBSUMPTION);
            }
            else
            {
                return new AssertSimpleHint(AssertSimpleHint.AssertSimpleType.CONJ);
            }
        }
    }


}
