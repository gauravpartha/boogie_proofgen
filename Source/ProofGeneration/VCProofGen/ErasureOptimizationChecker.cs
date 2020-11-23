using System.Collections.Generic;
using System.Transactions;
using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;

namespace ProofGeneration.VCProofGen
{
    public class ErasureOptimizationChecker : ReadOnlyVisitor
    {

        private bool _result;
        private int _withinNumQuantifier;
        private bool _hasTypeQuantification;

        /// <summary>
        /// returns false, if the erasure of e to a VCExpr does not use any optimizations
        /// if true is returned, then erasure may use optimizations (but not necessarily)
        /// </summary>
        public bool ErasureSimplifiesExpression(Expr e, out bool hasTypeQuantification)
        {
            _withinNumQuantifier = 0;
            _result = false;
            _hasTypeQuantification = false;
            Visit(e);
            var finalResult = _result;
            hasTypeQuantification = _hasTypeQuantification;
            return finalResult;
        }

        public override Expr VisitNAryExpr(NAryExpr node)
        {
            if (_withinNumQuantifier > 0 && node.Fun is BinaryOperator bop && bop.Op == BinaryOperator.Opcode.Imp)
            {
                _result = true;
            }

            return base.VisitNAryExpr(node);
        }

        public override QuantifierExpr VisitQuantifierExpr(QuantifierExpr node)
        {
            if (node.TypeParameters.Count > 0)
            {
                _result = true;
                _hasTypeQuantification = true;
            }
            
            _withinNumQuantifier++;
            Visit(node._Body);
            _withinNumQuantifier--;

            return node;
        }
    }
}