using System;
using Isabelle.Ast;
using Microsoft.Boogie;
using Type = Microsoft.Boogie.Type;

namespace ProofGeneration.Util
{
    public class ProofGenSubsetChecker : ResultReadOnlyVisitor<Term>
    {
        private object problematicNode;
        private bool result;

        protected override bool TranslatePrecondition(Absy node)
        {
            throw new NotImplementedException();
        }

        public bool ProofGenSupportsSubset(Program p, out object resultNode)
        {
            problematicNode = null;
            Visit(p);
            resultNode = problematicNode;
            return problematicNode == null;
        }

        public override Choice VisitChoice(Choice node)
        {
            problematicNode = node;
            return node;
        }

        public override Sequential VisitSequential(Sequential node)
        {
            problematicNode = node;
            return node;
        }

        public override Type VisitBvType(BvType node)
        {
            problematicNode = node;
            return node;
        }

        public override Expr VisitCodeExpr(CodeExpr node)
        {
            problematicNode = node;
            return node;
        }

        public override Expr VisitLambdaExpr(LambdaExpr node)
        {
            problematicNode = node;
            return node;
        }

        public override MapType VisitMapType(MapType node)
        {
            problematicNode = node;
            return node;
        }

        public override Cmd VisitRE(RE node)
        {
            problematicNode = node;
            return node;
        }

        public override Cmd VisitStateCmd(StateCmd node)
        {
            problematicNode = node;
            return node;
        }

        public override YieldCmd VisitYieldCmd(YieldCmd node)
        {
            problematicNode = node;
            return node;
        }

        public override Expr VisitBvConcatExpr(BvConcatExpr node)
        {
            problematicNode = node;
            return node;
        }

        public override Expr VisitBvExtractExpr(BvExtractExpr node)
        {
            problematicNode = node;
            return node;
        }

        public override Type VisitBvTypeProxy(BvTypeProxy node)
        {
            problematicNode = node;
            return node;
        }

        public override AssignLhs VisitMapAssignLhs(MapAssignLhs node)
        {
            problematicNode = node;
            return node;
        }

        public override Type VisitMapTypeProxy(MapTypeProxy node)
        {
            problematicNode = node;
            return node;
        }

        public override Cmd VisitParCallCmd(ParCallCmd node)
        {
            problematicNode = node;
            return node;
        }

        public override Type VisitFloatType(FloatType node)
        {
            problematicNode = node;
            return node;
        }

        public override AtomicRE VisitAtomicRE(AtomicRE node)
        {
            problematicNode = node;
            return node;
        }
    }
}