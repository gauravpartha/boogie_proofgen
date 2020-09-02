using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;
using System;
using System.Collections.Generic;

namespace ProofGeneration.VCProofGen
{
    class VCFunDeclCollector : TraversingVCExprVisitor<bool, bool>
    {
        private IDictionary<string, Function> nameToFunction;

        private IDictionary<Function, Function> funToVCfun;

        //returns map that maps each function f in the input functions for which there is a corresponding function in the VC with the same name
        // (to which f is mapped to in the dictionary)
        public IDictionary<Function, Function> CollectFunDeclarations(VCExpr node, IEnumerable<Function> functions)
        {
            nameToFunction = new Dictionary<string, Function>();
            foreach(var f in functions)
            {
                nameToFunction.Add(f.Name, f);
            }
            funToVCfun = new Dictionary<Function, Function>();

            node.Accept(this, true);
            return funToVCfun;
        }

        protected override bool StandardResult(VCExpr node, bool arg)
        {
            if(node is VCExprNAry vcExprNAry && vcExprNAry.Op is VCExprBoogieFunctionOp boogieFunOp)
            {
                if(nameToFunction.TryGetValue(boogieFunOp.Func.Name, out Function origFunction) && !funToVCfun.ContainsKey(origFunction))
                {
                    funToVCfun.Add(origFunction, boogieFunOp.Func);
                }
            }

            return true;
        }
    }
}
