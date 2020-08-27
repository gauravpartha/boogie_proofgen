using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;
using ProofGeneration.CFGRepresentation;

namespace ProofGeneration.VCProofGen
{
    class PassiveActiveDecl : IActiveDeclGenerator
    {
        public IDictionary<Block, ISet<NamedDeclaration>> GetActiveDeclsPerBlock(IDictionary<Block, VCExpr> blockToVC, IVCVarTranslator translator, CFGRepr cfg, out IDictionary<Block, ISet<Variable>> blockToNewVars)
        {
            var blockToDefinedDecls = new Dictionary<Block, ISet<NamedDeclaration>>();

            foreach (Block b in cfg.GetBlocksForwards())
            {
                blockToDefinedDecls.Add(b, new HashSet<NamedDeclaration>());
            }

            var declCollector = new VCExprDeclCollector();

            var blockToNamedDecls = new Dictionary<Block, ISet<NamedDeclaration>>();

            //compute all named declarations in the VC for each block b which have been used before b is reached
            foreach (Block b in cfg.GetBlocksForwards())
            {
                ISet<NamedDeclaration> bDecls = declCollector.CollectNamedDeclarations(blockToVC[b], translator);
                blockToNamedDecls.Add(b, bDecls);

                foreach (Block bSucc in cfg.GetSuccessorBlocks(b))
                {
                    blockToDefinedDecls[bSucc].UnionWith(bDecls);
                    blockToDefinedDecls[bSucc].UnionWith(blockToDefinedDecls[b]);
                }
            }

            //compute all named declarations in the VC for each block b that are in any path reached from b and which were defined in any path reaching b
            //named declarations which are not variables are trivially defined at the beginning of the CFG
            var blockToActiveDecls = new Dictionary<Block, ISet<NamedDeclaration>>();
            blockToNewVars = new Dictionary<Block, ISet<Variable>>();
            foreach (Block b in cfg.GetBlocksBackwards())
            {
                ISet<NamedDeclaration> bDecls = blockToNamedDecls[b];

                ISet<NamedDeclaration> oldActiveDecls = new HashSet<NamedDeclaration>();
                ISet<Variable> newDecls = new HashSet<Variable>();

                foreach (NamedDeclaration d in bDecls)
                {
                    if ((d is Variable v) && !blockToDefinedDecls[b].Contains(d))
                    {
                        newDecls.Add(v);
                    }
                    else
                    {
                        oldActiveDecls.Add(d);
                    }
                }

                blockToNewVars.Add(b, newDecls);

                foreach (Block bSucc in cfg.GetSuccessorBlocks(b))
                {
                    foreach (NamedDeclaration d in blockToActiveDecls[bSucc])
                    {
                        if (!newDecls.Contains(d))
                        {
                            oldActiveDecls.Add(d);
                        }
                    }
                }

                blockToActiveDecls[b] = oldActiveDecls;
            }

            return blockToActiveDecls;
        }
    }
}
