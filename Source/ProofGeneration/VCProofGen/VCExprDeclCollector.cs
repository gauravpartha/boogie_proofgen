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
        private IDictionary<string, NamedDeclaration> NameToDecl;

        public ISet<NamedDeclaration> CollectNamedDeclarations(VCExpr node, IDictionary<string, NamedDeclaration> NameToDecl)
        {
            this.NameToDecl = NameToDecl;
            this.NamedDeclarations = new HashSet<NamedDeclaration>();

            node.Accept(this, true);
            return this.NamedDeclarations;
        }

        protected override bool StandardResult(VCExpr node, bool arg)
        {
            if(node is VCExprVar varNode)
            {
                bool success = NameToDecl.TryGetValue(varNode.Name, out NamedDeclaration result);
                if (success)
                    NamedDeclarations.Add(result);                
            }

            return true;
        }
    }
}
