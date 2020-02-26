using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;
using ProofGeneration.CFGRepresentation;
using System.Collections.Generic;
using System.Linq;
using System.Diagnostics.Contracts;
using System;
using ProofGeneration.Isa;

namespace ProofGeneration.VCProofGen
{
    class VCBlockToIsaTranslator
    {
        private readonly UniqueNamer uniqueNamer;

        public VCBlockToIsaTranslator(UniqueNamer uniqueNamer)
        {
            this.uniqueNamer = uniqueNamer;            
        }

        public VCBlockToIsaTranslator() : this(new UniqueNamer())
        {
            uniqueNamer.Spacer = "_";
        }

        public IDictionary<Block, DefDecl> IsaDefsFromVC(IDictionary<Block, VCExpr> blockToVC, CFGRepr cfg, IEnumerable<Variable> inParams, IEnumerable<Variable> localVars)
        {
            Contract.Ensures(Contract.Result<IDictionary<Block, DefDecl>>().Count == cfg.GetBlocksBackwards().Count());

            ISet<string> programVariables = new HashSet<string>(inParams.Select(v => v.Name).Concat(localVars.Select(v => v.Name)));

            IDictionary<Block, DefDecl> blockToDefVC = new Dictionary<Block, DefDecl>();

            foreach(Block block in cfg.GetBlocksBackwards())
            {
                // might be more efficient to hand over this:
                // IEnumerable<Tuple<Block, DefDecl>> successorDefs = cfg.outgoingBlocks[block].Select(b => new Tuple<Block, DefDecl>(b, blockToDefVC[b]));

                var vcExprIsaVisitor = new VCExprToIsaTranslator(uniqueNamer, blockToDefVC);

                Term term = vcExprIsaVisitor.Translate(blockToVC[block]);

                DefDecl def = new DefDecl(GetVCDefName(block), new Tuple<IList<Term>, Term>(new List<Term>(), term));

                Contract.Assert(!blockToDefVC.ContainsKey(block));
                blockToDefVC.Add(block, def);
            }

            return blockToDefVC;            
        }

        public static string GetVCDefName(Block block)
        {
            return "vc_" + block.Label;
        }

    }
}
