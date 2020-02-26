using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace ProofGeneration.VCProofGen
{
    class VCExprDeclCollector : TraversingVCExprVisitor<bool, bool>
    {
        private ISet<NamedDeclaration> NamedDeclarations;        

        private IDictionary<VCExprVar, Variable> VcToVar;

        public ISet<NamedDeclaration> CollectNamedDeclarations(VCExpr node, IDictionary<VCExprVar, Variable> vcToVar)
        {
            this.VcToVar = vcToVar;
            this.NamedDeclarations = new HashSet<NamedDeclaration>();

            node.Accept(this, true);
            return this.NamedDeclarations;
        }

        protected override bool StandardResult(VCExpr node, bool arg)
        {
            if(node is VCExprVar varNode && VcToVar.TryGetValue(varNode, out Variable boogieVar))
            {
                 NamedDeclarations.Add(boogieVar);
            } else if(node is VCExprNAry vcExprNAry && vcExprNAry.Op is VCExprBoogieFunctionOp boogieFunOp)
            {
                NamedDeclarations.Add(boogieFunOp.Func);
            }

            return true;
        }
    }
}
