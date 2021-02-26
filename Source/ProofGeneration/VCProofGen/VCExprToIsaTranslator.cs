using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.Isa;
using ProofGeneration.Util;
using SimpleType = ProofGeneration.Isa.SimpleType;

namespace ProofGeneration.VCProofGen
{
    // argument is not used
    public class VCExprToIsaTranslator : IVCExprVisitor<Term, bool>
    {
        private readonly IDictionary<Block, IList<VCExprVar>> blockToActiveVars;

        protected readonly ISet<VCExprOp> criticalOps;

        private readonly PureTyIsaTransformer pureTyIsaTransformer = new PureTyIsaTransformer();
        private readonly IDictionary<Block, DefDecl> successorToVC;

        private readonly IsaUniqueNamer uniqueNamer;

        protected readonly VCExprOpIsaVisitor vcExprOpIsaVisitor = new VCExprOpIsaVisitor();

        private bool _tryInstantiatingFunctions;

        private readonly bool useNamesOfVarsForTranslation;

        /// <param name="uniqueNamer">namer to be used for vc variables</param>
        /// <param name="successorToVC"></param>
        /// <param name="blockToActiveVars"></param>
        /// <param name="useNamesOfVarsForTranslation">
        ///     if set to true, then <paramref name="uniqueNamer" /> will be applied
        ///     to the name of a vc variable instead of the object, also <see cref="CreateNameBasedTranslator" />
        /// </param>
        public VCExprToIsaTranslator(
            IsaUniqueNamer uniqueNamer,
            IDictionary<Block, DefDecl> successorToVC,
            IDictionary<Block, IList<VCExprVar>> blockToActiveVars,
            bool useNamesOfVarsForTranslation = false)
        {
            this.uniqueNamer = uniqueNamer;
            this.useNamesOfVarsForTranslation = useNamesOfVarsForTranslation;
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
        {
        }

        public Term Visit(VCExprLiteral node, bool arg)
        {
            if (node == VCExpressionGenerator.True)
                return new BoolConst(true);
            if (node == VCExpressionGenerator.False)
                return new BoolConst(false);
            if (node is VCExprIntLit lit)
                return new TermWithExplicitType(new IntConst(lit.Val), new PrimitiveType(SimpleType.Int));
            throw new NotImplementedException();
        }

        public Term Visit(VCExprNAry node, bool arg)
        {
            /* for operations where the VC ast subtree may be very large, we proceed using a stack and otherwise recursively */

            if (!IsCriticalOp(node.Op)) return VisitRecursive(node, arg);

            var todoStack = new Stack<VCExpr>();
            var activeNAryStack = new Stack<Tuple<VCExprNAry, List<Term>>>();
            //invariant: operation of nodes in activeNAryStack are critical
            todoStack.Push(node);

            Term result = null;

            while (todoStack.Count > 0)
            {
                var curExpr = todoStack.Pop();
                if (curExpr is VCExprNAry curNAry && IsCriticalOp(curNAry.Op))
                {
                    activeNAryStack.Push(Tuple.Create(curNAry, new List<Term>()));

                    foreach (var child in curNAry) todoStack.Push(child);
                }
                else
                {
                    activeNAryStack.Peek().Item2.Add(curExpr.Accept(this, arg));

                    //collapse activeNAry stack as much as possible
                    do
                    {
                        var top = activeNAryStack.Peek();

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
                        }
                        else
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

        public Term Visit(VCExprVar node, bool arg)
        {
            if (VCBlockExtractor.PredictBlockName(node.Name, out var predictedBlockName) &&
                TryGetDefFromBlock(predictedBlockName, out var block, out var def))
                return new TermApp(IsaCommonTerms.TermIdentFromName(def.name),
                    blockToActiveVars[block].Select(v => Translate(v)).ToList());

            return IsaCommonTerms.TermIdentFromName(GetVcVarName(node));
        }

        public Term Visit(VCExprQuantifier node, bool arg)
        {
            var body = Translate(node.Body);

            var boundVars = node.BoundVars.Select(v => (Identifier) new SimpleIdentifier(GetVcVarName(v))).ToList();

            return new TermQuantifier(ConvertQuantifierKind(node.Quan), boundVars, body);
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
                return IsaCommonTerms.Let(new SimpleIdentifier(GetVcVarName(elem.V)),
                    //pureTyIsaTransformer.Translate(elem.V.Type), 
                    Translate(elem.E),
                    prevBody
                );
            });
        }


        /// <summary>
        ///     Use this constructor if every VC variable with the same name should have the same representation.
        ///     In particular, this means that two different VC variable objects with the same name will be represented the same
        ///     way.
        ///     Only use this if you are either sure that names uniquely determine a VC variable (abstractly) or if you have some
        ///     other operation that fails if this were not the case.
        /// </summary>
        public static VCExprToIsaTranslator CreateNameBasedTranslator(IsaUniqueNamer uniqueNamer)
        {
            return new VCExprToIsaTranslator(uniqueNamer,
                new Dictionary<Block, DefDecl>(),
                new Dictionary<Block, IList<VCExprVar>>(),
                true);
        }

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

        private Term VisitRecursive(VCExprNAry node, bool arg)
        {
            var term = new List<Term>();
            foreach (var childNode in node) term.Add(childNode.Accept(this, arg));

            return GetTermFromNAry(node, term);
        }

        private Term GetTermFromNAry(VCExprNAry node, List<Term> args)
        {
            return node.Accept(vcExprOpIsaVisitor, args);
        }

        private bool IsCriticalOp(VCExprOp op)
        {
            return criticalOps.Contains(op);
        }

        private string GetVcVarName(VCExprVar vcVar)
        {
            if (useNamesOfVarsForTranslation) return uniqueNamer.GetName(vcVar.Name, vcVar.Name);

            return uniqueNamer.GetName(vcVar, vcVar.Name);
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

        private bool TryGetDefFromBlock(string blockName, out Block block, out DefDecl blockDef)
        {
            foreach (var kv in successorToVC)
                if (kv.Key.Label.Equals(blockName))
                {
                    block = kv.Key;
                    blockDef = kv.Value;
                    return true;
                }

            block = null;
            blockDef = null;
            return false;
        }
    }
}