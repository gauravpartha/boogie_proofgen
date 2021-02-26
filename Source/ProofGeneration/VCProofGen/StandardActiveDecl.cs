using System.Collections.Generic;
using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;
using ProofGeneration.CFGRepresentation;

namespace ProofGeneration.VCProofGen
{
    internal class StandardActiveDecl : IActiveDeclGenerator
    {
        public IDictionary<Block, ISet<NamedDeclaration>> GetActiveDeclsPerBlock(IDictionary<Block, VCExpr> blockToVC,
            IVCVarFunTranslator translator, CFGRepr cfg, out IDictionary<Block, ISet<Variable>> blockToNewVars)
        {
            var blockToDecls = new Dictionary<Block, ISet<NamedDeclaration>>();

            var declCollector = new VCExprDeclCollector();

            foreach (var b in cfg.GetBlocksBackwards())
            {
                var bDecls = declCollector.CollectNamedDeclarations(blockToVC[b], translator);
                foreach (var b_succ in cfg.GetSuccessorBlocks(b))
                    //flattening
                foreach (var sucDecl in blockToDecls[b_succ])
                    bDecls.Add(sucDecl);

                blockToDecls[b] = bDecls;
            }

            blockToNewVars = null;

            return blockToDecls;
        }
    }
}