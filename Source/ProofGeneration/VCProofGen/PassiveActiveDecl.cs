using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;
using ProofGeneration.CFGRepresentation;

namespace ProofGeneration.VCProofGen
{
    internal class PassiveActiveDecl : IActiveDeclGenerator
    {
        public IDictionary<Block, ISet<NamedDeclaration>> GetActiveDeclsPerBlock(IDictionary<Block, VCExpr> blockToVC,
            IVCVarFunTranslator translator, CFGRepr cfg, out IDictionary<Block, ISet<Variable>> blockToNewVars)
        {
            var blockToDefinedDecls = new Dictionary<Block, ISet<NamedDeclaration>>();

            foreach (var b in cfg.GetBlocksForwards()) blockToDefinedDecls.Add(b, new HashSet<NamedDeclaration>());

            var declCollector = new VCExprDeclCollector();

            var blockToNamedDecls = new Dictionary<Block, ISet<NamedDeclaration>>();

            //compute all named declarations in the VC for each block b which have been used before b is reached
            foreach (var b in cfg.GetBlocksForwards())
            {
                var bDecls = declCollector.CollectNamedDeclarations(blockToVC[b], translator);
                blockToNamedDecls.Add(b, bDecls);

                foreach (var bSucc in cfg.GetSuccessorBlocks(b))
                {
                    blockToDefinedDecls[bSucc].UnionWith(bDecls);
                    blockToDefinedDecls[bSucc].UnionWith(blockToDefinedDecls[b]);
                }
            }

            //compute all named declarations in the VC for each block b that are in any path reached from b and which were defined in any path reaching b
            //named declarations which are not variables are trivially defined at the beginning of the CFG
            var blockToActiveDecls = new Dictionary<Block, ISet<NamedDeclaration>>();
            blockToNewVars = new Dictionary<Block, ISet<Variable>>();
            foreach (var b in cfg.GetBlocksBackwards())
            {
                var bDecls = blockToNamedDecls[b];

                ISet<NamedDeclaration> oldActiveDecls = new HashSet<NamedDeclaration>();
                ISet<Variable> newDecls = new HashSet<Variable>();

                foreach (var d in bDecls)
                    if (d is Variable v && !blockToDefinedDecls[b].Contains(d))
                        newDecls.Add(v);
                    else
                        oldActiveDecls.Add(d);

                blockToNewVars.Add(b, newDecls);

                foreach (var bSucc in cfg.GetSuccessorBlocks(b))
                foreach (var d in blockToActiveDecls[bSucc])
                    if (!newDecls.Contains(d))
                        oldActiveDecls.Add(d);

                blockToActiveDecls[b] = oldActiveDecls;
            }

            return blockToActiveDecls;
        }
    }
}