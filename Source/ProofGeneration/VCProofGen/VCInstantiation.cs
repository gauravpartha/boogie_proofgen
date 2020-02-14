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
    public class VCInstantiation
    {
        private readonly string LocaleName;        

        private readonly IDictionary<Block, DefDecl> blockToDef;

        private readonly IList<NamedDeclaration> holeSpec;

        public VCInstantiation(IDictionary<Block, DefDecl> blockToDef, IList<NamedDeclaration> holeSpec) : this(blockToDef, holeSpec, "")
        {
        }

        public VCInstantiation(IDictionary<Block, DefDecl> blockToDef, IList<NamedDeclaration> holeSpec, string LocaleName)
        {
            Contract.Requires(blockToDef != null);
            Contract.Requires(holeSpec != null);
            Contract.Requires(LocaleName != null);
            
            this.blockToDef = blockToDef;
            this.holeSpec = holeSpec;
            this.LocaleName = LocaleName;
        }

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

            return IsaCommonTerms.TermIdentFromName((LocaleName.Count() > 0 ? LocaleName + "." : "") + blockToDef[block].name);
        }

    }
}
