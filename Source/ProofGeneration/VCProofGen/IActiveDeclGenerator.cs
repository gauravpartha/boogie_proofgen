using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;
using ProofGeneration.CFGRepresentation;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace ProofGeneration.VCProofGen
{
    interface IActiveDeclGenerator
    {

        /// <summary>
        /// returns for each block the set of declarations which it is parameterized by (i.e., must be instantiated it)
        /// if blockToNewVars is non-null, then for each block the variables which should be universally quantified for the corresponding block definition are given
        /// </summary>
        IDictionary<Block, ISet<NamedDeclaration>> GetActiveDeclsPerBlock(
            IDictionary<Block, VCExpr> blockToVC,
            IVCVarFunTranslator translator,
            CFGRepr cfg,
            out IDictionary<Block, ISet<Variable>> blockToNewVars);

    }
}