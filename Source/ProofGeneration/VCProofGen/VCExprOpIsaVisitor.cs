using Microsoft.Boogie.VCExprAST;
using System;
using System.Collections.Generic;

namespace ProofGeneration.VCProofGen
{
    class VCExprOpIsaVisitor : IVCExprOpVisitor<Term, List<Term>>
    {
        public Term VisitAddOp(VCExprNAry node, List<Term> arg)
        {
            return new TermNAry(arg, TermNAry.TermOpCode.ADD);
        }

        public Term VisitAndOp(VCExprNAry node, List<Term> arg)
        {
            return new TermNAry(arg, TermNAry.TermOpCode.AND);
        }

        public Term VisitBoogieFunctionOp(VCExprNAry node, List<Term> arg)
        {
            //TODO
            throw new NotImplementedException();
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
            return new TermNAry(arg, TermNAry.TermOpCode.EQ);
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
            throw new NotImplementedException();
        }

        public Term VisitGtOp(VCExprNAry node, List<Term> arg)
        {
            throw new NotImplementedException();
        }

        public Term VisitIfThenElseOp(VCExprNAry node, List<Term> arg)
        {
            throw new NotImplementedException();
        }

        public Term VisitImpliesOp(VCExprNAry node, List<Term> arg)
        {
            throw new NotImplementedException();
        }

        public Term VisitLabelOp(VCExprNAry node, List<Term> arg)
        {
            throw new NotImplementedException();
        }

        public Term VisitLeOp(VCExprNAry node, List<Term> arg)
        {
            return new TermNAry(arg, TermNAry.TermOpCode.LE);
        }

        public Term VisitLtOp(VCExprNAry node, List<Term> arg)
        {
            throw new NotImplementedException();
        }

        public Term VisitModOp(VCExprNAry node, List<Term> arg)
        {
            throw new NotImplementedException();
        }

        public Term VisitMulOp(VCExprNAry node, List<Term> arg)
        {
            throw new NotImplementedException();
        }

        public Term VisitNeqOp(VCExprNAry node, List<Term> arg)
        {
            throw new NotImplementedException();
        }

        public Term VisitNotOp(VCExprNAry node, List<Term> arg)
        {
            return new TermNAry(arg, TermNAry.TermOpCode.NOT);
        }

        public Term VisitOrOp(VCExprNAry node, List<Term> arg)
        {
            return new TermNAry(arg, TermNAry.TermOpCode.OR);
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
            throw new NotImplementedException();
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
