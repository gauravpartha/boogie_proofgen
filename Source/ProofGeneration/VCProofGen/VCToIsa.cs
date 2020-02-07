using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;
using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace ProofGeneration.VCProofGen
{
    // argument is not used
    class VCToIsa : IVCExprVisitor<Term, bool>
    {

        private readonly IDictionary<string, Term> successorToVC;

        protected readonly ISet<VCExprOp> criticalOps;

        protected readonly VCExprOpIsaVisitor vcExprOpIsaVisitor = new VCExprOpIsaVisitor();

        protected readonly ISet<string> programVariables;

        public VCToIsa(IDictionary<string, Term> successorToVC, ISet<string> programVariables)
        {
            this.successorToVC = successorToVC;
            this.programVariables = programVariables;

            criticalOps = new HashSet<VCExprOp>
            {
                VCExpressionGenerator.NotOp,
                VCExpressionGenerator.ImpliesOp,
                VCExpressionGenerator.AndOp,
                VCExpressionGenerator.OrOp
            };
        }

        public Term Visit(VCExprLiteral node, bool arg)
        {
            if (node == VCExpressionGenerator.True)
                return new BoolConst(true);
            else if (node == VCExpressionGenerator.False)
                return new BoolConst(false);
            else if (node is VCExprIntLit lit)
            {
                return new IntConst(lit.Val);
            } else
            {
                throw new NotImplementedException();
            }
        }

        public Term Visit(VCExprNAry node, bool arg)
        {
            /* for operations where the VC ast subtree may be very large, we proceed using a stack and otherwise recursively */             

            if(!IsCriticalOp(node.Op))
            {
                return VisitRecursive(node, arg);
            }

            var todoStack = new Stack<VCExpr>();
            var activeNAryStack = new Stack<VCExprNAry>();
            //invariant: operation of nodes in activeNAryStack are critical


            IList<Term> activeResults = new List<Term>();

            todoStack.Push(node);     

            while(todoStack.Count > 0)
            {                
                VCExpr curExpr = todoStack.Pop();
                if(curExpr is VCExprNAry curNAry && IsCriticalOp(curNAry.Op)) {
                    activeNAryStack.Push(curNAry);
                    foreach (var child in curNAry)
                    {
                        todoStack.Push(child);
                    }
                }
                else
                {
                    activeResults.Add(curExpr.Accept(this, arg));
                    if(activeNAryStack.Peek().Count() == activeResults.Count)
                    {
                        VCExprNAry topNAry = activeNAryStack.Pop();
                        //reverse children, since first one is added last
                        Term result = getTermFromNAry(topNAry, activeResults.Reverse().ToList());
                        activeResults = new List<Term>() { result };                        
                    }
                }
            }

            Contract.Assert(activeNAryStack.Count == 0);
            Contract.Assert(activeResults.Count == 1);

            return activeResults.First();
        }

        private Term VisitRecursive(VCExprNAry node, bool arg)
        {
            List<Term> term = new List<Term>();
            foreach(var childNode in node)
            {
                term.Add(childNode.Accept(this, arg));
            }

            return getTermFromNAry(node, term);
        }

        private Term getTermFromNAry(VCExprNAry node, List<Term> args)
        {
            return node.Accept(this.vcExprOpIsaVisitor, args);
        }

        private bool IsCriticalOp(VCExprOp op)
        {
            return this.criticalOps.Contains(op);
        }

        public Term Visit(VCExprVar node, bool arg)
        {
            bool success = successorToVC.TryGetValue(node.Name.Split('_')[0], out Term result);
            if (success)
                return result;
            else
                throw new ProofGenUnexpectedStateException<VCToIsa>(this.GetType(), "cannot resolve variable");
        }

        public Term Visit(VCExprQuantifier node, bool arg)
        {
            throw new NotImplementedException();
        }

        public Term Visit(VCExprLet node, bool arg)
        {
            throw new NotImplementedException();
        }
    }
}
