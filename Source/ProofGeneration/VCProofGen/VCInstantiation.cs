using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using Microsoft.Boogie;
using ProofGeneration.Isa;
using System.Diagnostics.Contracts;

namespace ProofGeneration.VCProofGen
{
    //instantiates vc block definitions correctly
    class VCInstantiation
    {
        private readonly string prefix;

        private readonly IDictionary<Block, DefDecl> blockToDef;

        private readonly IList<NamedDeclaration> holeSpec;

        public Term GetVCBlockInstantiation(Block block, IDictionary<NamedDeclaration, Term> declToVC)
        {    
            if(!blockToDef.ContainsKey(block))
            {
                throw new ProofGenUnexpectedStateException<VCInstantiation>(this.GetType(), "block unknown by vc");
            }

            IList<Term> args = new List<Term>();
            foreach(NamedDeclaration decl in holeSpec)
            {
                args.Add(declToVC[decl]);
            }

            return new TermApp(GetVCBlockRef(block), args);
        }

        public Term GetVCBlockRef(Block block)
        {
            Contract.Requires(block != null);
            Contract.Requires(blockToDef.ContainsKey(block));

            return IsaCommonTerms.TermIdentFromName(prefix + blockToDef[block].name);
        }

    }
}
