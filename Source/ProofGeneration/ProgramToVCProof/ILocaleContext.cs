using System.Collections.Generic;
using ProofGeneration.Isa;

namespace ProofGeneration.ProgramToVCProof
{
    public interface ILocaleContext
    {
        public ContextElem Context();
        public IList<OuterDecl> Prelude();
    }
}