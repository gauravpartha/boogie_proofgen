using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Isabelle.Ast;
using Isabelle.Util;
using Microsoft.Boogie.VCExprAST;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.Util;

namespace ProofGeneration.VCProofGen
{
    public class VCExprOpIsaVisitor : IVCExprOpVisitor<Term, List<Term>>
    {
        private readonly ConcreteTypeDeclTranslation _concreteTypeTranslation;

        private bool _tryInstantiatingTypes;

        private IsaUniqueNamer _uniqueNamer;

        public VCExprOpIsaVisitor(IsaUniqueNamer functionNamer)
        {
            _uniqueNamer = functionNamer;
            var boogieContext = new BoogieContextIsa(
                IsaCommonTerms.TermIdentFromName("A"),
                IsaCommonTerms.TermIdentFromName("M"),
                IsaCommonTerms.TermIdentFromName("\\<Lambda>"),
                IsaCommonTerms.TermIdentFromName("\\<Gamma>"),
                IsaCommonTerms.TermIdentFromName("\\<Omega>"));
            _concreteTypeTranslation = new ConcreteTypeDeclTranslation(boogieContext);
        }

        public VCExprOpIsaVisitor() : this(new IsaUniqueNamer())
        {
        }

        public Term VisitAddOp(VCExprNAry node, List<Term> arg)
        {
            return HandleBinaryOp(TermBinary.BinaryOpCode.Add, arg);
        }

        public Term VisitAndOp(VCExprNAry node, List<Term> arg)
        {
            return HandleBinaryOp(TermBinary.BinaryOpCode.And, arg);
        }

        public Term VisitBoogieFunctionOp(VCExprNAry node, List<Term> arg)
        {
            if (node.Op is VCExprBoogieFunctionOp funOp)
            {
                var name = funOp.Func.Name;
                if (_tryInstantiatingTypes &&
                    _concreteTypeTranslation.TryTranslateTypeDecl(funOp.Func, out var funTermResult))
                    return new TermApp(funTermResult, arg);
                return new TermApp(
                    IsaCommonTerms.TermIdentFromName(_uniqueNamer.GetName(funOp.Func.Name, funOp.Func.Name)), arg);
            }

            //should never reach this code
            Contract.Assert(false);
            return null;
        }

        public Term VisitBvConcatOp(VCExprNAry node, List<Term> arg)
        {
            throw new NotImplementedException();
        }

        public Term VisitBvExtractOp(VCExprNAry node, List<Term> arg)
        {
            throw new NotImplementedException();
        }

        public Term VisitBvOp(VCExprNAry node, List<Term> arg)
        {
            throw new NotImplementedException();
        }

        public Term VisitCustomOp(VCExprNAry node, List<Term> arg)
        {
            throw new NotImplementedException();
        }

        public Term VisitDistinctOp(VCExprNAry node, List<Term> arg)
        {
          Contract.Assert(arg.Count > 0);
          
          /* Since the arguments may have different types, we use a separate distinct term for each type (containing
             all elements that have that type). Since elements from different types are different, this accurately 
             reflects a distinct operator on all elements. */
          
          var argsWithTerm = node.Arguments.Zip(arg);
          var groupings =
            argsWithTerm.GroupBy(e => e.First.Type).ToArray();

          List<Term> distinctArgs = new List<Term>();

          foreach(var g in groupings)
          {
            var terms = g.ToList().Select(a => a.Second);
            distinctArgs.Add(IsaCommonTerms.Distinct(terms.ToList()));
          }

          var result = distinctArgs.Aggregate((result, term) => TermBinary.And(result, term));
          
          return result;
        }

        public Term VisitDivOp(VCExprNAry node, List<Term> arg)
        {
            Contract.Assert(arg.Count == 2);
            return new TermApp(IsaCommonTerms.TermIdentFromName("smt_div"), arg[0], arg[1]);
        }

        public Term VisitEqOp(VCExprNAry node, List<Term> arg)
        {
            return HandleBinaryOp(TermBinary.BinaryOpCode.Eq, arg);
        }

        public Term VisitFloatAddOp(VCExprNAry node, List<Term> arg)
        {
            throw new NotImplementedException();
        }

        public Term VisitFloatDivOp(VCExprNAry node, List<Term> arg)
        {
            throw new NotImplementedException();
        }

        public Term VisitFloatEqOp(VCExprNAry node, List<Term> arg)
        {
            throw new NotImplementedException();
        }

        public Term VisitFloatGeqOp(VCExprNAry node, List<Term> arg)
        {
            throw new NotImplementedException();
        }

        public Term VisitFloatGtOp(VCExprNAry node, List<Term> arg)
        {
            throw new NotImplementedException();
        }

        public Term VisitFloatLeqOp(VCExprNAry node, List<Term> arg)
        {
            throw new NotImplementedException();
        }

        public Term VisitFloatLtOp(VCExprNAry node, List<Term> arg)
        {
            throw new NotImplementedException();
        }

        public Term VisitFloatMulOp(VCExprNAry node, List<Term> arg)
        {
            throw new NotImplementedException();
        }

        public Term VisitFloatNeqOp(VCExprNAry node, List<Term> arg)
        {
            throw new NotImplementedException();
        }

        public Term VisitFloatSubOp(VCExprNAry node, List<Term> arg)
        {
            throw new NotImplementedException();
        }

        public Term VisitGeOp(VCExprNAry node, List<Term> arg)
        {
            return HandleBinaryOp(TermBinary.BinaryOpCode.Ge, arg);
        }

        public Term VisitGtOp(VCExprNAry node, List<Term> arg)
        {
            return HandleBinaryOp(TermBinary.BinaryOpCode.Gt, arg);
        }

        public Term VisitIfThenElseOp(VCExprNAry node, List<Term> arg)
        {
          if (arg.Count != 3)
          {
            throw new ProofGenUnexpectedStateException("VisitIfThenElseOp not invoked with three arguments");
          }
          
          //TODO: potentially put if-then-else expressions into the InnerAST directly
          return new TermApp(IsaCommonTerms.TermIdentFromName("ite_vc"), arg[0], arg[1], arg[2]);
        }

        public Term VisitImpliesOp(VCExprNAry node, List<Term> arg)
        {
            return HandleBinaryOp(TermBinary.BinaryOpCode.Implies, arg);
        }

        public Term VisitLeOp(VCExprNAry node, List<Term> arg)
        {
            return HandleBinaryOp(TermBinary.BinaryOpCode.Le, arg);
        }

        public Term VisitLtOp(VCExprNAry node, List<Term> arg)
        {
            return HandleBinaryOp(TermBinary.BinaryOpCode.Lt, arg);
        }

        public Term VisitModOp(VCExprNAry node, List<Term> arg)
        {
            throw new NotImplementedException();
        }

        public Term VisitMulOp(VCExprNAry node, List<Term> arg)
        {
            return HandleBinaryOp(TermBinary.BinaryOpCode.Mul, arg);
        }

        public Term VisitNeqOp(VCExprNAry node, List<Term> arg)
        {
            return HandleBinaryOp(TermBinary.BinaryOpCode.Neq, arg);
        }

        public Term VisitNotOp(VCExprNAry node, List<Term> arg)
        {
            return HandleUnaryOp(TermUnary.UnaryOpCode.Not, arg);
        }

        public Term VisitOrOp(VCExprNAry node, List<Term> arg)
        {
            return HandleBinaryOp(TermBinary.BinaryOpCode.Or, arg);
        }

        public Term VisitPowOp(VCExprNAry node, List<Term> arg)
        {
            throw new NotImplementedException();
        }

        public Term VisitRealDivOp(VCExprNAry node, List<Term> arg)
        {
            Contract.Assert(arg.Count == 2);
            return new TermApp(IsaCommonTerms.TermIdentFromName("smt_real_div"), arg[0], arg[1]);
        }

        public Term VisitSelectOp(VCExprNAry node, List<Term> arg)
        {
            throw new NotImplementedException();
        }

        public Term VisitStoreOp(VCExprNAry node, List<Term> arg)
        {
            throw new NotImplementedException();
        }

        public Term VisitSubOp(VCExprNAry node, List<Term> arg)
        {
            return HandleBinaryOp(TermBinary.BinaryOpCode.Sub, arg);
        }

        public Term VisitSubtype3Op(VCExprNAry node, List<Term> arg)
        {
            throw new NotImplementedException();
        }

        public Term VisitSubtypeOp(VCExprNAry node, List<Term> arg)
        {
            throw new NotImplementedException();
        }

        public Term VisitToIntOp(VCExprNAry node, List<Term> arg)
        {
            throw new NotImplementedException();
        }

        public Term VisitToRealOp(VCExprNAry node, List<Term> arg)
        {
            Contract.Assert(arg.Count == 1);
            return new TermApp(IsaCommonTerms.RealOfInt, arg[0]);
        }

        public void setFunctionNamer(IsaUniqueNamer functionNamer)
        {
            _uniqueNamer = functionNamer;
        }

        public void SetTryInstantiatingTypes(bool flag)
        {
            _tryInstantiatingTypes = flag;
        }

        public Term HandleBinaryOp(TermBinary.BinaryOpCode bop, List<Term> arg)
        {
            Contract.Assert(arg.Count == 2);
            return new TermBinary(arg[0], arg[1], bop);
        }

        public Term HandleUnaryOp(TermUnary.UnaryOpCode uop, List<Term> arg)
        {
            Contract.Assert(arg.Count == 1);
            return new TermUnary(arg[0], uop);
        }

        public Term VisitLabelOp(VCExprNAry node, List<Term> arg)
        {
            throw new NotImplementedException();
        }
    }
}