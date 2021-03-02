using System;
using System.Collections.Generic;
using Isabelle.Ast;
using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;

namespace ProofGeneration.VCProofGen
{
    public class VcRewriteLemmaGen
    {
        private readonly ErasureOptimizationChecker _erasureOptimizationChecker = new ErasureOptimizationChecker();
        private readonly TypePremiseEraserFactory _typeEraserFactory;
        private readonly VCExprToIsaTranslator _vcToIsaTranslator;

        private int _lemmaId;

        public VcRewriteLemmaGen(TypePremiseEraserFactory factory, VCExprToIsaTranslator vcToIsaTranslator)
        {
            _typeEraserFactory = factory;
            _vcToIsaTranslator = vcToIsaTranslator;
        }

        /// <summary>
        ///     Checks whether the VC for <paramref name="expr" /> is optimized w.r.t. standard translation and if so returns
        ///     true and stores the possible lemmas to rewrite back to a standard form in <paramref name="rewriteLemmas" />
        /// </summary>
        /// <param name="expr">expression that is translated to vc</param>
        /// <param name="proveVc">true if want to show that vc holds, false if given vc</param>
        /// <param name="rewriteLemmas"></param>
        /// <returns></returns>
        public bool RequiredVcRewrite(Expr expr, bool proveVc, out List<LemmaDecl> rewriteLemmas)
        {
            //TODO: make check more precise
            if (_erasureOptimizationChecker.ErasureSimplifiesExpression(expr, out var hasTypeQuantification))
            {
                rewriteLemmas = RewriteVcLemmas(expr, proveVc, hasTypeQuantification);
                return true;
            }

            rewriteLemmas = null;
            return false;
        }

        /// <summary>
        ///     return declarations to rewrite vc expression
        /// </summary>
        private List<LemmaDecl> RewriteVcLemmas(Expr expr, bool proveVc, bool hasTypeQuantification)
        {
            // To be safe create new erasers (erasers have state that change when certain methods are applied)
            /* Note that vcExtracted is supposed to be the same as directly erasing translatedVcExpr. The reason we
             translate the Boogie expression again to a VC expression before erasing it, is that erasure of a VCExpr
             has side effects on that VCExpr. 
             */
            Func<bool, int, VCExpr> eraseToVc = (b, i) =>
                _typeEraserFactory.NewEraser(b).TranslateAndErase(expr, i);

            bool lhsExtractArgs;
            string proofMethod;
            if (proveVc)
            {
                /* Prove vcNotOptimized ==> vcOptimized.
                 * This is the easier direction, because the type quantifiers in the premise can be directly instantiated
                 * with the extracted versions. */
                lhsExtractArgs = false;
                if (hasTypeQuantification)
                    proofMethod = "unfolding Let_def using prim_type_vc_lemmas by blast";
                else
                    proofMethod = "by blast";
            }
            else
            {
                /* Prove vcOptimized ==> vcNotOptimized.
                 * This is the harder direction. */
                lhsExtractArgs = true;
                if (hasTypeQuantification)
                    proofMethod = "using vc_extractor_lemmas by smt";
                else
                    proofMethod = "by blast";
            }

            var lemmaNameNeg = "expr_equiv_" + _lemmaId + "_neg";
            var lemmaNamePos = "expr_equiv_" + _lemmaId + "_pos";
            _lemmaId++;

            var lhsNeg = _vcToIsaTranslator.Translate(eraseToVc(lhsExtractArgs, -1));
            var lhsPos = _vcToIsaTranslator.Translate(eraseToVc(lhsExtractArgs, 1));

            var rhsNeg = _vcToIsaTranslator.Translate(eraseToVc(!lhsExtractArgs, -1));
            var rhsPos = _vcToIsaTranslator.Translate(eraseToVc(!lhsExtractArgs, 1));

            var result = new List<LemmaDecl>
            {
                new LemmaDecl(lemmaNameNeg, TermBinary.MetaImplies(lhsNeg, rhsNeg),
                    new Proof(new List<string> {proofMethod})),
                new LemmaDecl(lemmaNamePos, TermBinary.MetaImplies(lhsPos, rhsPos),
                    new Proof(new List<string> {proofMethod}))
            };
            return result;
        }
    }
}