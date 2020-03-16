using Microsoft.Boogie;
using ProofGeneration.Isa;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace ProofGeneration.ProgramToVCProof
{
    interface IBlockLemmaManager
    {
        LemmaDecl GenerateBlockLemma(Block block, IEnumerable<Block> successors, string lemmaName);

        LemmaDecl GenerateEmptyBlockLemma(Block block, IEnumerable<Block> successors, string lemmaName);

        ContextElem Context();

        IList<OuterDecl> Prelude();
    }
}
