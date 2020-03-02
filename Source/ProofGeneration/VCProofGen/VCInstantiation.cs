using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
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

        //blocks are only parameterized by those declarations which appear in them, i.e. this should a subset of holeSpec
        private readonly IDictionary<Block, ISet<NamedDeclaration>> blockToDecls;

        public VCInstantiation(
            IDictionary<Block, DefDecl> blockToDef, 
            IList<NamedDeclaration> holeSpec, 
            IDictionary<Block, ISet<NamedDeclaration>> blockToDecls) : this(blockToDef, holeSpec, blockToDecls, "")
        {
        }

        public VCInstantiation(
            IDictionary<Block, DefDecl> blockToDef, 
            IList<NamedDeclaration> holeSpec, 
            IDictionary<Block, ISet<NamedDeclaration>> blockToDecls, 
            string LocaleName)
        {
            Contract.Requires(blockToDef != null);
            Contract.Requires(holeSpec != null);
            Contract.Requires(blockToDecls != null);
            Contract.Requires(LocaleName != null);
            
            this.blockToDef = blockToDef;
            this.holeSpec = holeSpec;
            this.blockToDecls = blockToDecls;
            this.LocaleName = LocaleName;
        }

        public Term GetVCBlockInstantiation(Block block, IDictionary<NamedDeclaration, TermIdent> declToVC)
        {    
            if(!blockToDef.ContainsKey(block))
            {
                throw new ProofGenUnexpectedStateException(this.GetType(), "block unknown by vc");
            }

            IList<Term> args = new List<Term>();
            foreach(NamedDeclaration decl in holeSpec)
            {
                if (blockToDecls[block].Contains(decl))
                {                    
                    args.Add(declToVC[decl]);
                }
            }

            return new TermApp(GetVCBlockRef(block), args);
        }

        public Term GetVCBlockRef(Block block, bool qualified = true)
        {
            Contract.Requires(block != null);
            Contract.Requires(blockToDef.ContainsKey(block));

            return IsaCommonTerms.TermIdentFromName(GetVCBlockNameRef(block, qualified));
        }

        public string GetVCBlockNameRef(Block block, bool qualified = true)
        {
            Contract.Requires(block != null);
            Contract.Requires(blockToDef.ContainsKey(block));

            string prefix = (qualified && LocaleName.Count() > 0) ? LocaleName + "." : "";

            return prefix + blockToDef[block].name;
        }

    }
}
