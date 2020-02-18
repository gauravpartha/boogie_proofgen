using Microsoft.Boogie.VCExprAST;
using ProofGeneration.Isa;
using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace ProofGeneration.VCProofGen
{
    class VCExprOpIsaVisitor : IVCExprOpVisitor<Term, List<Term>>
    {

        public Term HandleBinaryOp(TermBinary.BinaryOpCode bop, List<Term> arg)
        {
            Contract.Assert(arg.Count == 2);
            return new TermBinary(arg[0], arg[1], bop);
        }

        public Term HandleUnaryOp(TermUnary.UnaryOpCode up, List<Term> arg)
        {
            Contract.Assert(arg.Count == 1);
            return new TermUnary(arg[0]);
        }

        public Term VisitAddOp(VCExprNAry node, List<Term> arg)
        {
            return HandleBinaryOp(TermBinary.BinaryOpCode.ADD, arg);
        }

        public Term VisitAndOp(VCExprNAry node, List<Term> arg)
        {
            return HandleBinaryOp(TermBinary.BinaryOpCode.AND, arg);
        }

        public Term VisitBoogieFunctionOp(VCExprNAry node, List<Term> arg)
        {
            if(node.Op is VCExprBoogieFunctionOp funOp) {
                return new TermApp(IsaCommonTerms.TermIdentFromName(funOp.Func.Name), arg);
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
            throw new NotImplementedException();
        }

        public Term VisitDivOp(VCExprNAry node, List<Term> arg)
        {
            throw new NotImplementedException();
        }

        public Term VisitEqOp(VCExprNAry node, List<Term> arg)
        {
            return HandleBinaryOp(TermBinary.BinaryOpCode.EQ, arg);
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
            return HandleBinaryOp(TermBinary.BinaryOpCode.GE, arg);
        }

        public Term VisitGtOp(VCExprNAry node, List<Term> arg)
        {
            return HandleBinaryOp(TermBinary.BinaryOpCode.GT, arg);
        }

        public Term VisitIfThenElseOp(VCExprNAry node, List<Term> arg)
        {
            throw new NotImplementedException();
        }

        public Term VisitImpliesOp(VCExprNAry node, List<Term> arg)
        {
            return HandleBinaryOp(TermBinary.BinaryOpCode.IMPLIES, arg);
        }

        public Term VisitLabelOp(VCExprNAry node, List<Term> arg)
        {
            throw new NotImplementedException();
        }

        public Term VisitLeOp(VCExprNAry node, List<Term> arg)
        {
            return HandleBinaryOp(TermBinary.BinaryOpCode.LE, arg);
        }

        public Term VisitLtOp(VCExprNAry node, List<Term> arg)
        {
            return HandleBinaryOp(TermBinary.BinaryOpCode.LT, arg);
        }

        public Term VisitModOp(VCExprNAry node, List<Term> arg)
        {
            throw new NotImplementedException();
        }

        public Term VisitMulOp(VCExprNAry node, List<Term> arg)
        {
            return HandleBinaryOp(TermBinary.BinaryOpCode.MUL, arg);
        }

        public Term VisitNeqOp(VCExprNAry node, List<Term> arg)
        {
            throw new NotImplementedException();
        }

        public Term VisitNotOp(VCExprNAry node, List<Term> arg)
        {
            return HandleUnaryOp(TermUnary.UnaryOpCode.NOT, arg);
        }

        public Term VisitOrOp(VCExprNAry node, List<Term> arg)
        {
            return HandleBinaryOp(TermBinary.BinaryOpCode.OR, arg);
        }

        public Term VisitPowOp(VCExprNAry node, List<Term> arg)
        {
            throw new NotImplementedException();
        }

        public Term VisitRealDivOp(VCExprNAry node, List<Term> arg)
        {
            throw new NotImplementedException();
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
            return HandleBinaryOp(TermBinary.BinaryOpCode.SUB, arg);
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
            throw new NotImplementedException();
        }
    }
}
