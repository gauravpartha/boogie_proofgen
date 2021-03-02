using System.Collections.Generic;
using Isabelle.Ast;
using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;

namespace ProofGeneration.VCProofGen
{
    public class VCHintManager
    {
        private readonly IDictionary<Block, VCHintBlock> _blockTo = new Dictionary<Block, VCHintBlock>();
        private readonly VcRewriteLemmaGen _vcRewriteLemmaGen;

        public VCHintManager(VcRewriteLemmaGen vcRewriteLemmaGen)
        {
            _vcRewriteLemmaGen = vcRewriteLemmaGen;
        }

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
            List<LemmaDecl> requiredDecls;

            if (cmd is AssumeCmd assumeCmd)
                vcHint = AssumeStmtHint(assumeCmd, exprVC, postVC, resultVC, out requiredDecls);
            else if (cmd is AssertCmd assertCmd)
                vcHint = AssertStmtHint(assertCmd, exprVC, postVC, subsumption, out requiredDecls);
            else
                throw new ProofGenUnexpectedStateException(GetType(), "expected an assert or assume cmd");

            if (!_blockTo.TryGetValue(block, out var vcHintBlock))
            {
                vcHintBlock = new VCHintBlock(block);
                _blockTo.Add(block, vcHintBlock);
            }

            if (requiredDecls != null) vcHintBlock.AddRequiredDecls(requiredDecls);

            vcHintBlock.AddHint(cmd, vcHint);
        }

        /// <summary>
        ///     If vc hints for <paramref name="block" /> exist, then return them. <paramref name="block" /> must be a
        ///     block in the final CFG used by Boogie (otherwise hints will not be found).
        /// </summary>
        public bool TryGetHints(Block block, out IEnumerable<VCHint> hints, out IEnumerable<OuterDecl> requiredDecls)
        {
            if (_blockTo.TryGetValue(block, out var vcHintBlock))
            {
                hints = vcHintBlock.Hints();
                requiredDecls = vcHintBlock.OuterDecls;

                return true;
            }

            hints = null;
            requiredDecls = null;
            return false;
        }

        /// <summary>
        ///     If no lemma is required for the proof, then <paramref name="decl" /> is null.
        /// </summary>
        private VCHint AssumeStmtHint(AssumeCmd assumeCmd, VCExpr exprVC, VCExpr postVC, VCExpr resultVC,
            out List<LemmaDecl> decl)
        {
            if (IsSpecialAssumeStmt(assumeCmd, exprVC, postVC, out var specialHint))
            {
                decl = null;
                return specialHint;
            }

            _vcRewriteLemmaGen.RequiredVcRewrite(assumeCmd.Expr, true, out decl);

            if (resultVC is VCExprNAry vcNAry && vcNAry.Op == VCExpressionGenerator.ImpliesOp)
            {
                var vcLeft = vcNAry[0];
                var nestLevel = 0;

                while (vcLeft != exprVC && vcLeft is VCExprNAry vcLeftNAry &&
                       vcLeftNAry.Op == VCExpressionGenerator.AndOp)
                {
                    vcLeft = vcLeftNAry[0];
                    nestLevel++;
                }

                if (vcLeft == exprVC)
                {
                    if (nestLevel == 0) return new AssumeConjHint(0, 0, 1, new VCExprHint(decl));
                    {
                        return new AssumeConjHint(nestLevel, nestLevel, -1, new VCExprHint(decl));
                    }
                }

                throw new ProofGenUnexpectedStateException(GetType(),
                    "cannot find assume expression on left hand side of vc implication");
            }

            throw new ProofGenUnexpectedStateException(GetType(), "unexpected vc of assume statement at top level");
        }

        /// <summary>
        ///     check whether assumeCmd is special with respect to VC and if so, store hint in out parameter, otherwise
        ///     store null in <paramref name="hint" />
        /// </summary>
        /// <returns>true, if is a special case <paramref name="hint" />, false otherwise</returns>
        private bool IsSpecialAssumeStmt(AssumeCmd assumeCmd, VCExpr exprVC, VCExpr postVC, out VCHint hint)
        {
            if (exprVC.Equals(VCExpressionGenerator.False))
            {
                hint = new AssumeSimpleHint(AssumeSimpleHint.AssumeSimpleType.ASSUME_FALSE);
                return true;
            }

            if (postVC.Equals(VCExpressionGenerator.False))
            {
                hint = new AssumeSimpleHint(AssumeSimpleHint.AssumeSimpleType.ASSUME_NOT);
                return true;
            }

            if (exprVC.Equals(VCExpressionGenerator.True) || postVC.Equals(VCExpressionGenerator.True))
            {
                hint = new AssumeSimpleHint(AssumeSimpleHint.AssumeSimpleType.ASSUME_TRUE);
                return true;
            }

            hint = null;
            return false;
        }

        /// <summary>
        ///     If no lemma is required for the proof, then <paramref name="decl" /> is null.
        /// </summary>
        private VCHint AssertStmtHint(
            AssertCmd cmd,
            VCExpr exprVC,
            VCExpr postVC,
            CommandLineOptions.SubsumptionOption subsumption,
            out List<LemmaDecl> requiredDecls)
        {
            requiredDecls = null;

            if (exprVC.Equals(VCExpressionGenerator.False) || postVC.Equals(VCExpressionGenerator.False))
                return new AssertSimpleHint(AssertSimpleHint.AssertSimpleType.ASSERT_FALSE);

            if (exprVC.Equals(VCExpressionGenerator.True))
                return new AssertSimpleHint(AssertSimpleHint.AssertSimpleType.ASSERT_TRUE);

            if (postVC.Equals(VCExpressionGenerator.True))
            {
                _vcRewriteLemmaGen.RequiredVcRewrite(cmd.Expr, false, out requiredDecls);
                return new AssertSimpleHint(AssertSimpleHint.AssertSimpleType.NO_CONJ, new VCExprHint(requiredDecls));
            }

            _vcRewriteLemmaGen.RequiredVcRewrite(cmd.Expr, false, out requiredDecls);
            if (
                subsumption == CommandLineOptions.SubsumptionOption.Always ||
                subsumption == CommandLineOptions.SubsumptionOption.NotForQuantifiers && !(exprVC is VCExprQuantifier)
            )
                return new AssertSimpleHint(AssertSimpleHint.AssertSimpleType.SUBSUMPTION,
                    new VCExprHint(requiredDecls));
            return new AssertSimpleHint(AssertSimpleHint.AssertSimpleType.CONJ, new VCExprHint(requiredDecls));
        }
    }
}