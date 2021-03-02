using System.Collections.Generic;
using Isabelle.Ast;
using Microsoft.Boogie;

namespace ProofGeneration.CfgToDag
{
    public class TypingHint
    {
        public TypingHint(
            IEnumerable<DefDecl> substHint,
            IEnumerable<Variable> requiredVars,
            IEnumerable<Function> requiredFuncs
        )
        {
        }
    }
}