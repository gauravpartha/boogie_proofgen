using System.Collections.Generic;
using Microsoft.Boogie;
using ProofGeneration.Isa;

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