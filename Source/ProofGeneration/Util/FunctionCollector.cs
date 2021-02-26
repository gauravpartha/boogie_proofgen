using System.Collections.Generic;
using Microsoft.Boogie;

namespace ProofGeneration.Util
{
    public class FunctionCollector : ResultReadOnlyVisitor<bool>
    {
        private List<Function> _functions;

        protected override bool TranslatePrecondition(Absy node)
        {
            return node is Expr;
        }

        public IEnumerable<Function> UsedFunctions(Expr e)
        {
            _functions = new List<Function>();
            Visit(e);
            return _functions;
        }

        public override Expr VisitNAryExpr(NAryExpr node)
        {
            if (node.Fun is FunctionCall fc) _functions.Add(fc.Func);

            return base.VisitNAryExpr(node);
        }
    }
}