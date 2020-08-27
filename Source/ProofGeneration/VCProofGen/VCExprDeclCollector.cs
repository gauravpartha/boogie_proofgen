using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;
using System.Collections.Generic;

namespace ProofGeneration.VCProofGen
{
    class VCExprDeclCollector : TraversingVCExprVisitor<bool, bool>
    {
        private ISet<NamedDeclaration> NamedDeclarations;        

        private IVCVarTranslator translator;

        public ISet<NamedDeclaration> CollectNamedDeclarations(VCExpr node, IVCVarTranslator translator)
        {
            this.translator = translator;
            NamedDeclarations = new HashSet<NamedDeclaration>();

            node.Accept(this, true);
            return NamedDeclarations;
        }

        protected override bool StandardResult(VCExpr node, bool arg)
        {
            if(node is VCExprVar varNode && translator.TranslateVCVar(varNode, out Variable boogieVar))
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
