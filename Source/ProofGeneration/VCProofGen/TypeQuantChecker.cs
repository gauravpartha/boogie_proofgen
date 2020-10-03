using Microsoft.Boogie;

namespace ProofGeneration.VCProofGen
{
    public class TypeQuantChecker : ReadOnlyVisitor
    {

        private bool _result = false;

        public bool HasTypeQuantification(Expr e)
        {
            _result = false;
            Visit(e);
            var finalResult = _result;
            _result = false;
            return finalResult;
        }

        public override QuantifierExpr VisitQuantifierExpr(QuantifierExpr node)
        {
            if (node.TypeParameters.Count > 0)
            {
                _result = true;
            }
            else
            {
                Visit(node._Body);
            }

            return node;
        }
    }
}