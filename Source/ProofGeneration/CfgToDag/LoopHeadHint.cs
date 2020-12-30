using System.Collections.Generic;
using Microsoft.Boogie;

namespace ProofGeneration.CfgToDag
{
    public class LoopHeadHint
    {
        public IEnumerable<Variable> ModifiedVars { get; }
        public IEnumerable<Expr> Invariants { get; }

        public LoopHeadHint(IEnumerable<Variable> modifiedVars, IEnumerable<Expr> invariants)
        {
            ModifiedVars = modifiedVars;
            Invariants = invariants;
        }
    }
}