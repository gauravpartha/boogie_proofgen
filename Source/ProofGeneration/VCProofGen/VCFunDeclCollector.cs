using System.Collections.Generic;
using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;

namespace ProofGeneration.VCProofGen
{
    internal class VCFunDeclCollector : TraversingVCExprVisitor<bool, bool>
    {
        private IDictionary<Function, Function> funToVCfun;
        private IDictionary<string, Function> nameToFunction;

        public IDictionary<Function, Function> CollectFunDeclarations(VCExpr vcExpr, IEnumerable<Function> functions)
        {
            return CollectFunDeclarations(new List<VCExpr> {vcExpr}, functions);
        }

        //returns map that maps each function f in the input functions for which there is a corresponding function in the VC with the same name
        // (to which f is mapped to in the dictionary)
        public IDictionary<Function, Function> CollectFunDeclarations(IEnumerable<VCExpr> vcExprs,
            IEnumerable<Function> functions)
        {
            nameToFunction = new Dictionary<string, Function>();
            foreach (var f in functions) nameToFunction.Add(f.Name, f);
            funToVCfun = new Dictionary<Function, Function>();

            foreach (var vcExpr in vcExprs) vcExpr.Accept(this, true);

            return funToVCfun;
        }

        protected override bool StandardResult(VCExpr node, bool arg)
        {
            if (node is VCExprNAry vcExprNAry && vcExprNAry.Op is VCExprBoogieFunctionOp boogieFunOp)
                if (nameToFunction.TryGetValue(boogieFunOp.Func.Name, out var origFunction) &&
                    !funToVCfun.ContainsKey(origFunction))
                    funToVCfun.Add(origFunction, boogieFunOp.Func);

            return true;
        }
    }
}