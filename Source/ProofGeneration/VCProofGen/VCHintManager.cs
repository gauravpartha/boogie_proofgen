using System;
using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;
using System.Collections.Generic;
using ProofGeneration.Isa;
using ProofGeneration.Util;

namespace ProofGeneration.VCProofGen
{
    
    public class VCHintManager
    {
        private int _lemmaId = 0;
        private readonly ErasureOptimizationChecker _erasureOptimizationChecker = new ErasureOptimizationChecker();
        
        private readonly IDictionary<Block, VCHintBlock> _blockTo = new Dictionary<Block, VCHintBlock>();

        public static VCHint AssertConjHint = new AssertSimpleHint(AssertSimpleHint.AssertSimpleType.CONJ);
        public static VCHint AssertNoConjHint = new AssertSimpleHint(AssertSimpleHint.AssertSimpleType.NO_CONJ);
        public static VCHint AssertSubsumptionHint = new AssertSimpleHint(AssertSimpleHint.AssertSimpleType.SUBSUMPTION);

        private readonly TypePremiseEraserFactory _typeEraserFactory;
        private readonly VCExprToIsaTranslator _vcToIsaTranslator;

        public VCHintManager(TypePremiseEraserFactory typeEraserFactory, VCExprToIsaTranslator vcToIsaTranslator)
        {
            _typeEraserFactory = typeEraserFactory;
            _vcToIsaTranslator = vcToIsaTranslator;
            _vcToIsaTranslator.SetTryInstantiatingFunctions(true);
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
            {
                vcHint = AssumeStmtHint(assumeCmd, exprVC, postVC, resultVC, out requiredDecls);
            } else if (cmd is AssertCmd assertCmd)
            {
                vcHint = AssertStmtHint(assertCmd, exprVC, postVC, subsumption, out requiredDecls);
            } else
            {
                throw new ProofGenUnexpectedStateException(GetType(), "expected an assert or assume cmd");
            }

            if (!_blockTo.TryGetValue(block, out VCHintBlock vcHintBlock))
            {
                vcHintBlock = new VCHintBlock(block);
                _blockTo.Add(block, vcHintBlock);
            }

            if (requiredDecls != null)
            {
                vcHintBlock.AddRequiredDecls(requiredDecls);                
            }
            
            vcHintBlock.AddHint(cmd, vcHint);
        }
        
        /// <summary>
        /// return declarations to rewrite vc expression
        /// </summary>
        private List<LemmaDecl> RewriteVcLemmas(Expr expr, VCExpr translatedVcExpr, bool isAssumeCmd,
            bool hasTypeQuantification)
        {
            // To be safe create new erasers (erasers have state that change when certain methods are applied)
            /* Note that vcExtracted is supposed to be the same as directly erasing translatedVcExpr. The reason we
             translate the Boogie expression again to a VC expression before erasing it, is that erasure of a VCExpr
             has side effects on that VCExpr. 
             */
            //TODO: figure out when the polarity can have an effect on the expression
            Func<bool, int, VCExpr> eraseToVc = (b, i) =>
                _typeEraserFactory.NewEraser(b).TranslateAndErase(expr, i);

            bool lhsExtractArgs;
            string proofMethod;
            if (isAssumeCmd)
            {
                /* Using the Boogie expression need to prove that the extracted vc expr holds, but want to instead prove
                 * that the non-extracted vc expr holds: Prove vcNotExtracted ==> vcExtracted.
                 * This is the harder direction. */
                lhsExtractArgs = false;
                if (hasTypeQuantification)
                    proofMethod = "unfolding Let_def using prim_type_vc_lemmas by blast";
                else
                    proofMethod = "by blast";
            }
            else
            {
                /* Using the extracted VC expression, need to prove the Boogie expression holds, but want to use the
                 * non-extracted VC expression holds: Prove vcExtracted ==> vcNotExtracted.
                 * This is the easier direction, because the type quantifiers in the premise can be directly instantiated
                 * with the extracted versions. */
                lhsExtractArgs = true;
                if (hasTypeQuantification)
                    proofMethod = "using vc_extractor_lemmas by smt";
                else
                    proofMethod = "by blast";
            }

            var lemmaNameNeg = "expr_equiv_" + _lemmaId + "_neg";
            var lemmaNamePos= "expr_equiv_" + _lemmaId + "_pos";
            _lemmaId++;

            Term lhsNeg = _vcToIsaTranslator.Translate(eraseToVc(lhsExtractArgs, -1));
            Term lhsPos = _vcToIsaTranslator.Translate(eraseToVc(lhsExtractArgs, 1));
            
            Term rhsNeg = _vcToIsaTranslator.Translate(eraseToVc(!lhsExtractArgs, -1));
            Term rhsPos = _vcToIsaTranslator.Translate(eraseToVc(!lhsExtractArgs, 1));

            var result = new List<LemmaDecl>
            {
                new LemmaDecl(lemmaNameNeg, TermBinary.MetaImplies(lhsNeg, rhsNeg),
                    new Proof(new List<string> {proofMethod})),
                new LemmaDecl(lemmaNamePos, TermBinary.MetaImplies(lhsPos, rhsPos),
                    new Proof(new List<string> {proofMethod}))
            };
            return result;
        }
        public bool TryGetHints(Block block, out IEnumerable<VCHint> hints, out IEnumerable<OuterDecl> requiredDecls)
        {
            if (_blockTo.TryGetValue(block, out VCHintBlock vcHintBlock))
            {
                hints = vcHintBlock.Hints();
                requiredDecls = vcHintBlock.OuterDecls;
                
                return true;
            }
            else
            {
                hints = null;
                requiredDecls = null;
                return false;
            }
        }

        /// <summary>
        /// If no lemma is required for the proof, then <paramref name="decl"/> is null.
        /// </summary>
        private VCHint AssumeStmtHint(AssumeCmd assumeCmd, VCExpr exprVC, VCExpr postVC, VCExpr resultVC, out List<LemmaDecl> decl)
        {
            if(IsSpecialAssumeStmt(assumeCmd, exprVC, postVC, out VCHint specialHint))
            {
                decl = null;
                return specialHint;
            }

            if (_erasureOptimizationChecker.ErasureSimplifiesExpression(assumeCmd.Expr, out bool hasTypeQuantification))
            {
                decl = RewriteVcLemmas(assumeCmd.Expr, exprVC, true, hasTypeQuantification);
            }
            else
            {
                decl = null;
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
                        return new AssumeConjHint(0, 0, 1, new VCExprHint(decl));
                    }
                    {
                        return new AssumeConjHint(nestLevel, nestLevel, -1, new VCExprHint(decl));
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
        /// store null in <paramref name="hint"/>
        /// </summary>
        /// <returns>true, if is a special case <paramref name="hint"/>, false otherwise</returns>
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

        /// <summary>
        /// If no lemma is required for the proof, then <paramref name="decl"/> is null.
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
            {
                return new AssertSimpleHint(AssertSimpleHint.AssertSimpleType.ASSERT_FALSE);
            }
            else if (exprVC.Equals(VCExpressionGenerator.True))
            {
                return new AssertSimpleHint(AssertSimpleHint.AssertSimpleType.ASSERT_TRUE);
            }
            else if (postVC.Equals(VCExpressionGenerator.True))
            {
               if (_erasureOptimizationChecker.ErasureSimplifiesExpression(cmd.Expr, out bool hasTypeQuantification))
               {
                   requiredDecls = RewriteVcLemmas(cmd.Expr, exprVC, false, hasTypeQuantification);
               }
               return new AssertSimpleHint(AssertSimpleHint.AssertSimpleType.NO_CONJ, new VCExprHint(requiredDecls));
            }
            else
            {
               if (_erasureOptimizationChecker.ErasureSimplifiesExpression(cmd.Expr, out bool hasTypeQuantification))
               {
                   requiredDecls = RewriteVcLemmas(cmd.Expr, exprVC, false, hasTypeQuantification);
               }
               if (
                   subsumption == CommandLineOptions.SubsumptionOption.Always ||
                   (subsumption == CommandLineOptions.SubsumptionOption.NotForQuantifiers && !(exprVC is VCExprQuantifier))
               )
               {
                   return new AssertSimpleHint(AssertSimpleHint.AssertSimpleType.SUBSUMPTION, new VCExprHint(requiredDecls));
               }
               else
               {
                   return new AssertSimpleHint(AssertSimpleHint.AssertSimpleType.CONJ, new VCExprHint(requiredDecls));
               }
            }
        }
    }


}
