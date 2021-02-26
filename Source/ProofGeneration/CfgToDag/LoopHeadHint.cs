using System.Collections.Generic;
using Microsoft.Boogie;

namespace ProofGeneration.CfgToDag
{
    public class LoopHeadHint
    {
        public LoopHeadHint(IEnumerable<Variable> modifiedVars, IEnumerable<Expr> invariants)
        {
            ModifiedVars = modifiedVars;
            Invariants = invariants;
        }

        public IEnumerable<Variable> ModifiedVars { get; }
        public IEnumerable<Expr> Invariants { get; }
    }
}