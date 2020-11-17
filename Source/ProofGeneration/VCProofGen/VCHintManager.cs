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
            OuterDecl requiredDecl;
            
            if (cmd is AssumeCmd assumeCmd)
            {
                vcHint = AssumeStmtHint(assumeCmd, exprVC, postVC, resultVC, out LemmaDecl requiredDecl1);
                requiredDecl = requiredDecl1;
            } else if (cmd is AssertCmd assertCmd)
            {
                vcHint = AssertStmtHint(assertCmd, exprVC, postVC, subsumption, out LemmaDecl requiredDecl2);
                requiredDecl = requiredDecl2;
            } else
            {
                throw new ProofGenUnexpectedStateException(GetType(), "expected an assert or assume cmd");
            }

            if (!_blockTo.TryGetValue(block, out VCHintBlock vcHintBlock))
            {
                vcHintBlock = new VCHintBlock(block);
                _blockTo.Add(block, vcHintBlock);
            }

            if (requiredDecl != null)
            {
                vcHintBlock.AddRequiredDecl(requiredDecl);                
            }
            
            vcHintBlock.AddHint(cmd, vcHint);
        }
        
        /// <summary>
        /// return Isabelle lemma with which one can exchange vc expression required for proof 
        /// </summary>
        private LemmaDecl LemmaForVc(Expr expr, VCExpr translatedVcExpr, bool isAssumeCmd)
        {
            // To be safe create new erasers (erasers have state that change when certain methods are applied)
            /* Note that vcExtracted is supposed to be the same as directly erasing translatedVcExpr. The reason we
             translate the Boogie expression again to a VC expression before erasing it, is that erasure of a VCExpr
             has side effects on that VCExpr. 
             */
            VCExpr vcExtracted = _typeEraserFactory.NewEraser(true).TranslateAndErase(expr);
            VCExpr vcNotExtracted = _typeEraserFactory.NewEraser(false).TranslateAndErase(expr);
            
            Term lhs, rhs;
            if (isAssumeCmd)
            {
                // using the Boogie expression need to prove that the extracted vc expr holds, but want to instead prove
                // that the non-extracted vc expr holds: Prove vcNotExtracted ==> vcExtracted
                lhs = _vcToIsaTranslator.Translate(vcNotExtracted);
                rhs = _vcToIsaTranslator.Translate(vcExtracted);
            }
            else
            {
                // using the extracted VC expression, need to prove the Boogie expression holds, but want to use the
                // non-extracted VC expression holds: Prove vcExtracted ==> vcNotExtracted
                lhs = _vcToIsaTranslator.Translate(vcExtracted);
                rhs = _vcToIsaTranslator.Translate(vcNotExtracted);
            }

            var lemmaName = "expr_equiv_" + _lemmaId;
            _lemmaId++;

            return new LemmaDecl(lemmaName, TermBinary.MetaImplies(lhs, rhs), new Proof(new List<string> {"unfolding Let_def", "by clarsimp"}));
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
        private VCHint AssumeStmtHint(AssumeCmd assumeCmd, VCExpr exprVC, VCExpr postVC, VCExpr resultVC, out LemmaDecl decl)
        {
            if(IsSpecialAssumeStmt(assumeCmd, exprVC, postVC, out VCHint specialHint))
            {
                decl = null;
                return specialHint;
            }

            if (_erasureOptimizationChecker.ErasureSimplifiesExpression(assumeCmd.Expr))
            {
                decl = LemmaForVc(assumeCmd.Expr, exprVC, true);
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
            out LemmaDecl requiredDecl)
        {
            requiredDecl = null;

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
               if (_erasureOptimizationChecker.ErasureSimplifiesExpression(cmd.Expr))
               {
                   requiredDecl = LemmaForVc(cmd.Expr, exprVC, false);
               }
               return new AssertSimpleHint(AssertSimpleHint.AssertSimpleType.NO_CONJ, new VCExprHint(requiredDecl));
            }
            else
            {
               if (_erasureOptimizationChecker.ErasureSimplifiesExpression(cmd.Expr))
               {
                   requiredDecl = LemmaForVc(cmd.Expr, exprVC, false);
               }
               if (
                   subsumption == CommandLineOptions.SubsumptionOption.Always ||
                   (subsumption == CommandLineOptions.SubsumptionOption.NotForQuantifiers && !(exprVC is VCExprQuantifier))
               )
               {
                   return new AssertSimpleHint(AssertSimpleHint.AssertSimpleType.SUBSUMPTION, new VCExprHint(requiredDecl));
               }
               else
               {
                   return new AssertSimpleHint(AssertSimpleHint.AssertSimpleType.CONJ, new VCExprHint(requiredDecl));
               }
            }
        }
    }


}
