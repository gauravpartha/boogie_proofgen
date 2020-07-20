using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;
using ProofGeneration.CFGRepresentation;
using System.Collections.Generic;
using System.Linq;
using System.Diagnostics.Contracts;
using System;
using ProofGeneration.Isa;
using ProofGeneration.Util;
using ProofGeneration.BoogieIsaInterface;

namespace ProofGeneration.VCProofGen
{
    class VCBlockToIsaTranslator
    {
        private readonly IsaUniqueNamer uniqueNamer;

        private readonly PureTyIsaTransformer pureTyIsaTransformer = new PureTyIsaTransformer();

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
            IEnumerable<Variable> inParams, 
            IEnumerable<Variable> localVars, 
            IDictionary<Block, IList<VCExprVar>> blockToNewVars = null)
        {
            Contract.Ensures(Contract.Result<IDictionary<Block, DefDecl>>().Count == cfg.NumOfBlocks());

            ISet<string> programVariables = new HashSet<string>(inParams.Select(v => v.Name).Concat(localVars.Select(v => v.Name)));

            IDictionary<Block, DefDecl> blockToDefVC = new Dictionary<Block, DefDecl>();

            foreach(Block block in cfg.GetBlocksBackwards())
            {
                // might be more efficient to hand over this:
                // IEnumerable<Tuple<Block, DefDecl>> successorDefs = cfg.outgoingBlocks[block].Select(b => new Tuple<Block, DefDecl>(b, blockToDefVC[b]));

                var vcExprIsaVisitor = new VCExprToIsaTranslator(uniqueNamer, blockToDefVC, blockToActiveVars);

                Term term = vcExprIsaVisitor.Translate(blockToVC[block]);

                if (blockToNewVars != null && blockToNewVars.TryGetValue(block, out IList<VCExprVar> newVars) && newVars != null && newVars.Any())
                {
                    IList<Identifier> boundVars = newVars.Select(v => (Identifier) new SimpleIdentifier(uniqueNamer.GetName(v, v.Name))).ToList();
                    IList<TypeIsa> boundVarsTypes = newVars.Select(v => pureTyIsaTransformer.Translate(v.Type)).ToList();

                    term = new TermQuantifier(TermQuantifier.QuantifierKind.ALL, boundVars, boundVarsTypes, term);
                }

                IList<Term> args = blockToActiveVars[block].Select(v => vcExprIsaVisitor.Translate(v)).ToList();

                DefDecl def = new DefDecl(GetVCDefName(block), new Tuple<IList<Term>, Term>(args, term));

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
