using System;
using System.Collections.Generic;
using Microsoft.Boogie;

namespace ProofGeneration.Passification
{
  /// <summary>
  ///     Copy and minor adjustments from <see cref="OldFinder" /> (which is not accessible).
  /// </summary>
  public class OldVarFinder : ReadOnlyVisitor
    {
        private GSet<Variable> _freeOldVars;
        private Predicate<Variable> _pred;

        /// <summary>
        ///     Returns all variables which are occur within an old expression in <paramref name="node" />
        ///     and which satisfy <paramref name="pred" />
        /// </summary>
        public ISet<Variable> FindOldVariables(Absy node, Predicate<Variable> pred)
        {
            _freeOldVars = new GSet<Variable>();
            _pred = pred;
            Visit(node);
            return new HashSet<Variable>(_freeOldVars);
        }

        public override Expr VisitOldExpr(OldExpr node)
        {
            var freeVars = new GSet<object>();
            node.Expr.ComputeFreeVariables(freeVars);
            foreach (var v in freeVars)
                // Note, "v" is either a Variable or a TypeVariable
                if (v is Variable vVar && _pred(vVar))
                    _freeOldVars.Add(vVar);

            return node; // don't visit subexpressions, since ComputeFreeVariables has already gone through those
        }
    }
}