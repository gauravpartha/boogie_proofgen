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
        private readonly string localeName;        

        private readonly IDictionary<Block, DefDecl> blockToDef;

        //blocks are only parameterized by those declarations which appear in them, i.e. this should a subset of holeSpec
        private readonly IDictionary<Block, IList<NamedDeclaration>> blockToDecls;

        public VCInstantiation(
            IDictionary<Block, DefDecl> blockToDef, 
            IDictionary<Block, IList<NamedDeclaration>> blockToDecls) : this(blockToDef, blockToDecls, "")
        {
        }

        public VCInstantiation(
            IDictionary<Block, DefDecl> blockToDef, 
            IDictionary<Block, IList<NamedDeclaration>> blockToDecls, 
            string localeName)
        {
            Contract.Requires(blockToDef != null);
            Contract.Requires(blockToDecls != null);
            Contract.Requires(localeName != null);
            
            this.blockToDef = blockToDef;
            this.blockToDecls = blockToDecls;
            this.localeName = localeName;
        }

        public Term GetVCBlockInstantiation(Block block, IDictionary<NamedDeclaration, TermIdent> declToVC)
        {
            return GetVCBlockInstantiation(block, decl => declToVC[decl]);
        }

        public Term GetVCBlockInstantiation(Block block, Func<NamedDeclaration, TermIdent> declToVC)
        {    
            if(!blockToDef.ContainsKey(block))
            {
                throw new ProofGenUnexpectedStateException(this.GetType(), "block unknown by vc");
            }

            IList<NamedDeclaration> activeDecls = blockToDecls[block];

            IList<Term> args = new List<Term>();
            foreach(NamedDeclaration decl in activeDecls)
            {
                args.Add(declToVC(decl));
            }

            return new TermApp(GetVCBlockRef(block), args);
        }

        public IList<NamedDeclaration> GetVCBlockParameters(Block block)
        {
            if (!blockToDecls.ContainsKey(block))
            {
                throw new ProofGenUnexpectedStateException(this.GetType(), "block unknown by vc");
            }

            return blockToDecls[block];
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

            string prefix = (qualified && localeName.Count() > 0) ? localeName + "." : "";

            return prefix + blockToDef[block].name;
        }

    }
}
