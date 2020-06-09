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
        //If vcHintsName is null, then no hints are provided. All other parameters must be non-null.
        LemmaDecl GenerateBlockLemma(Block block, IEnumerable<Block> sucPassive, string lemmaName, string vcHintsName);

        LemmaDecl GenerateEmptyBlockLemma(Block block, IEnumerable<Block> sucPassive, string lemmaName);

        ContextElem Context();

        IList<OuterDecl> Prelude();
    }
}
