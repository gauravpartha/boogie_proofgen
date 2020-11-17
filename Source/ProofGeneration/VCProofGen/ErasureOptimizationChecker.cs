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

        /// <summary>
        /// returns false, if the erasure of e to a VCExpr does not use any optimizations
        /// if true is returned, then erasure may use optimizations (but not necessarily)
        /// </summary>
        public bool ErasureSimplifiesExpression(Expr e)
        {
            _withinNumQuantifier = 0;
            _result = false;
            Visit(e);
            var finalResult = _result;
            _result = false;
            return finalResult;
        }

        public override Expr VisitNAryExpr(NAryExpr node)
        {
            if (_withinNumQuantifier > 0 && node.Fun is BinaryOperator bop && bop.Op == BinaryOperator.Opcode.Imp)
            {
                _result = true;
                return node;
            }

            return base.VisitNAryExpr(node);
        }

        public override QuantifierExpr VisitQuantifierExpr(QuantifierExpr node)
        {
            if (node.TypeParameters.Count > 0)
            {
                _result = true;
            }
            else
            {
                _withinNumQuantifier++;
                Visit(node._Body);
                _withinNumQuantifier--;
            }

            return node;
        }
    }
}