using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;
using System.Collections.Generic;

namespace ProofGeneration.VCProofGen
{
    class VCExprDeclCollector : TraversingVCExprVisitor<bool, bool>
    {
        private ISet<NamedDeclaration> NamedDeclarations;        

        private IVCVarFunTranslator translator;

        public ISet<NamedDeclaration> CollectNamedDeclarations(VCExpr node, IVCVarFunTranslator translator)
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
                if(translator.TranslateVCFunction(boogieFunOp.Func, out Function boogieFun))
                {
                    NamedDeclarations.Add(boogieFun);
                } else
                {
                    //function does not appear in the Boogie program and is some VC specific function
                    NamedDeclarations.Add(boogieFunOp.Func);
                }
            }

            return true;
        }
    }
}
