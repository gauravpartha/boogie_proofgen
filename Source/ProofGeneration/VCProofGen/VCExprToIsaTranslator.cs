using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;
using ProofGeneration.Isa;
using ProofGeneration.Util;
using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using ProofGeneration.BoogieIsaInterface;

namespace ProofGeneration.VCProofGen
{
    // argument is not used
    public class VCExprToIsaTranslator : IVCExprVisitor<Term, bool>
    {
        private readonly IDictionary<Block, DefDecl> successorToVC;

        protected readonly ISet<VCExprOp> criticalOps;

        protected readonly VCExprOpIsaVisitor vcExprOpIsaVisitor = new VCExprOpIsaVisitor();

        private readonly IDictionary<Block, IList<VCExprVar>> blockToActiveVars;

        private readonly IsaUniqueNamer uniqueNamer;

        private readonly PureTyIsaTransformer pureTyIsaTransformer = new PureTyIsaTransformer();

        private bool _tryInstantiatingFunctions = false;

        public VCExprToIsaTranslator(IsaUniqueNamer uniqueNamer, IDictionary<Block, DefDecl> successorToVC, IDictionary<Block, IList<VCExprVar>> blockToActiveVars)
        {
            this.uniqueNamer = uniqueNamer;
            this.successorToVC = successorToVC;
            this.blockToActiveVars = blockToActiveVars;

            criticalOps = new HashSet<VCExprOp>
            {
                VCExpressionGenerator.NotOp,
                VCExpressionGenerator.ImpliesOp,
                VCExpressionGenerator.AndOp,
                VCExpressionGenerator.OrOp
            };
        }

        public VCExprToIsaTranslator(IsaUniqueNamer uniqueNamer) : 
            this(uniqueNamer, new Dictionary<Block, DefDecl>(), new Dictionary<Block, IList<VCExprVar>>())
        { }
        public void SetTryInstantiatingFunctions(bool flag)
        {
            _tryInstantiatingFunctions = flag;
            vcExprOpIsaVisitor.SetTryInstantiatingTypes(flag);
        }

        public void SetFunctionNamer(IsaUniqueNamer functionNamer)
        {
            vcExprOpIsaVisitor.setFunctionNamer(functionNamer);
        }

        public Term Translate(VCExpr node)
        {
            Contract.Requires(node != null);
            return node.Accept(this, true);
        }

        public Term Visit(VCExprLiteral node, bool arg)
        {
            if (node == VCExpressionGenerator.True)
                return new BoolConst(true);
            else if (node == VCExpressionGenerator.False)
                return new BoolConst(false);
            else if (node is VCExprIntLit lit)
            {
                return new TermWithExplicitType(new IntConst(lit.Val), new PrimitiveType(Isa.SimpleType.Int));
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
            var activeNAryStack = new Stack<Tuple<VCExprNAry, List<Term>>>();
            //invariant: operation of nodes in activeNAryStack are critical
            todoStack.Push(node);

            Term result = null;

            while(todoStack.Count > 0)
            {                
                VCExpr curExpr = todoStack.Pop();
                if(curExpr is VCExprNAry curNAry && IsCriticalOp(curNAry.Op)) {
                    activeNAryStack.Push(Tuple.Create(curNAry, new List<Term>()));

                    foreach (var child in curNAry)
                    {
                        todoStack.Push(child);
                    }
                }
                else
                {
                    activeNAryStack.Peek().Item2.Add(curExpr.Accept(this, arg));

                    //collapse activeNAry stack as much as possible
                    do
                    {
                        Tuple<VCExprNAry, List<Term>> top = activeNAryStack.Peek();

                        if (top.Item1.Count() == top.Item2.Count())
                        {
                            activeNAryStack.Pop();

                            //reverse children, since first one is added last
                            top.Item2.Reverse();
                            var newResult = GetTermFromNAry(top.Item1, top.Item2);
                            if (activeNAryStack.Count() > 0)
                                activeNAryStack.Peek().Item2.Add(newResult);
                            else
                                result = newResult;
                        } else
                        {
                            Contract.Assert(todoStack.Count > 0);
                            break;
                        }
                    } while (activeNAryStack.Count > 0);
                }
            }

            Contract.Assert(activeNAryStack.Count == 0);
            Contract.Assert(result != null);

            return result;
        }

        private Term VisitRecursive(VCExprNAry node, bool arg)
        {
            List<Term> term = new List<Term>();
            foreach(var childNode in node)
            {
                term.Add(childNode.Accept(this, arg));
            }

            return GetTermFromNAry(node, term);
        }

        private Term GetTermFromNAry(VCExprNAry node, List<Term> args)
        {
            return node.Accept(this.vcExprOpIsaVisitor, args);
        }

        private bool IsCriticalOp(VCExprOp op)
        {
            return this.criticalOps.Contains(op);
        }

        public Term Visit(VCExprVar node, bool arg)
        {
            if (VCBlockExtractor.PredictBlockName(node.Name, out string predictedBlockName) &&
                     TryGetDefFromBlock(predictedBlockName, out Block block, out DefDecl def))
            {
                return new TermApp(IsaCommonTerms.TermIdentFromName(def.name), blockToActiveVars[block].Select(v => Translate(v)).ToList());
            }
            else
                return IsaCommonTerms.TermIdentFromName(uniqueNamer.GetName(node, node.Name));
        }

        public Term Visit(VCExprQuantifier node, bool arg)
        {
            Term body = Translate(node.Body);

            List<Identifier> boundVars = node.BoundVars.Select(v => (Identifier) new SimpleIdentifier(uniqueNamer.GetName(v, v.Name))).ToList();

            return new TermQuantifier(ConvertQuantifierKind(node.Quan), boundVars, body);
        }

        private TermQuantifier.QuantifierKind ConvertQuantifierKind(Quantifier quantifier)
        {
            switch (quantifier)
            {
                case Quantifier.ALL:
                    return TermQuantifier.QuantifierKind.ALL;
                case Quantifier.EX:
                    return TermQuantifier.QuantifierKind.EX;
                default:
                    throw new ProofGenUnexpectedStateException(GetType(), "unexpected vc quantifier");
            }
        }

        public Term Visit(VCExprLet node, bool arg)
        {
            /* translate multi-binder let expression into multiple single-binder let expressions
             * reverse first, since we want to fold right
             */
            return node.Reverse().Aggregate(Translate(node.Body), (prevBody, elem) =>
            {
                /* don't provide explicit type annotations for simplicity, since in certain cases would have to translate
                 the actual type to something else (such as when it is the type variable 't, but we would want closed_ty)
                 */
                return IsaCommonTerms.Let(new SimpleIdentifier(uniqueNamer.GetName(elem.V, elem.V.Name)),
                     //pureTyIsaTransformer.Translate(elem.V.Type), 
                    Translate(elem.E),
                    prevBody
                );
            });
        }

        private bool TryGetDefFromBlock(string blockName, out Block block, out DefDecl blockDef)
        {
            foreach(var kv in successorToVC)
            {
                if(kv.Key.Label.Equals(blockName))
                {
                    block = kv.Key;
                    blockDef = kv.Value;
                    return true;
                }
            }

            block = null; blockDef = null;
            return false;
        }
    }
}
