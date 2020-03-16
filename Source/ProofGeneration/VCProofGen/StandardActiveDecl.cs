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
    class StandardActiveDecl : IActiveDeclGenerator
    {
        public IDictionary<Block, ISet<NamedDeclaration>> GetActiveDeclsPerBlock(IDictionary<Block, VCExpr> blockToVC, IDictionary<VCExprVar, Variable> vcToBoogieVar, CFGRepr cfg, out IDictionary<Block, ISet<Variable>> blockToNewVars)
        {
            var blockToDecls = new Dictionary<Block, ISet<NamedDeclaration>>();

            var declCollector = new VCExprDeclCollector();

            foreach (Block b in cfg.GetBlocksBackwards())
            {
                ISet<NamedDeclaration> bDecls = declCollector.CollectNamedDeclarations(blockToVC[b], vcToBoogieVar);
                foreach (Block b_succ in cfg.GetSuccessorBlocks(b))
                {
                    //flattening
                    foreach (var sucDecl in blockToDecls[b_succ])
                    {
                        bDecls.Add(sucDecl);
                    }
                }

                blockToDecls[b] = bDecls;
            }

            blockToNewVars = null;

            return blockToDecls;
        }
    }
}
