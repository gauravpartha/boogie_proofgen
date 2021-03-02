using System.Collections.Generic;
using Isabelle.Ast;

namespace ProofGeneration.ProgramToVCProof
{
    public interface ILocaleContext
    {
        public ContextElem Context();
        public IList<OuterDecl> Prelude();
    }
}