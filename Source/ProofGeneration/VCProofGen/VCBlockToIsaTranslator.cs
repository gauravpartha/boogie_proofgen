using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.CFGRepresentation;
using ProofGeneration.Isa;
using ProofGeneration.Util;

namespace ProofGeneration.VCProofGen
{
    internal class VCBlockToIsaTranslator
    {
        private readonly PureTyIsaTransformer pureTyIsaTransformer = new PureTyIsaTransformer();
        private readonly IsaUniqueNamer uniqueNamer;

        public VCBlockToIsaTranslator(IsaUniqueNamer uniqueNamer)
        {
            this.uniqueNamer = uniqueNamer;
        }

        public VCBlockToIsaTranslator() : this(new IsaUniqueNamer())
        {
        }


        //if blockToNewVars is non-null, then the mapped variables are universally quantified for the corresponding block definition
        public IDictionary<Block, DefDecl> IsaDefsFromVC(IDictionary<Block, VCExpr> blockToVC,
            IDictionary<Block, IList<VCExprVar>> blockToActiveVars,
            CFGRepr cfg,
            IDictionary<Block, IList<VCExprVar>> blockToNewVars = null)
        {
            Contract.Ensures(Contract.Result<IDictionary<Block, DefDecl>>().Count == cfg.NumOfBlocks());

            IDictionary<Block, DefDecl> blockToDefVC = new Dictionary<Block, DefDecl>();

            var vcExprIsaVisitor = new VCExprToIsaTranslator(uniqueNamer, blockToDefVC, blockToActiveVars);

            foreach (var block in cfg.GetBlocksBackwards())
            {
                // might be more efficient to hand over this:
                // IEnumerable<Tuple<Block, DefDecl>> successorDefs = cfg.outgoingBlocks[block].Select(b => new Tuple<Block, DefDecl>(b, blockToDefVC[b]));

                var term = vcExprIsaVisitor.Translate(blockToVC[block]);

                if (blockToNewVars != null && blockToNewVars.TryGetValue(block, out var newVars) && newVars != null &&
                    newVars.Any())
                {
                    IList<Identifier> boundVars = newVars
                        .Select(v => (Identifier) new SimpleIdentifier(uniqueNamer.GetName(v, v.Name))).ToList();
                    IList<TypeIsa> boundVarsTypes =
                        newVars.Select(v => pureTyIsaTransformer.Translate(v.Type)).ToList();

                    term = new TermQuantifier(TermQuantifier.QuantifierKind.ALL, boundVars, boundVarsTypes, term);
                }

                IList<Term> args = blockToActiveVars[block].Select(v => vcExprIsaVisitor.Translate(v)).ToList();

                var def = new DefDecl(GetVCDefName(block), new Tuple<IList<Term>, Term>(args, term));

                Contract.Assert(!blockToDefVC.ContainsKey(block));
                blockToDefVC.Add(block, def);
            }

            return blockToDefVC;
        }

        private string GetVCDefName(Block block)
        {
            return uniqueNamer.GetName(block, "vc_" + block.Label);
        }
    }
}