using System;
using Microsoft.Boogie;
using ProofGeneration.Isa;
using Type = Microsoft.Boogie.Type;

namespace ProofGeneration.ProgramToVCProof
{
    internal class PureToBoogieValConverter : ResultReadOnlyVisitor<Func<Term, Term>>
    {
        public Term ConvertToBoogieVal(Type ty, Term pureVal)
        {
            return Translate(ty)(pureVal);
        }

        protected override bool TranslatePrecondition(Absy node)
        {
            return node is Type;
        }

        public override Type VisitTypeVariable(TypeVariable node)
        {
            //instantiate T@U with the Boogie values means we do not need to transform the value
            ReturnResult(v => v);
            return node;
        }

        public override CtorType VisitCtorType(CtorType node)
        {
            //instantiate T@U with the Boogie values means we do not need to transform the value
            ReturnResult(v => v);
            return node;
        }

        public override Type VisitBasicType(BasicType node)
        {
            if (node.IsBool)
                ReturnResult(v => IsaBoogieTerm.BoolVal(v));
            else if (node.IsInt)
                ReturnResult(v => IsaBoogieTerm.IntVal(v));
            else
                throw new NotImplementedException();

            return node;
        }

        public override Type VisitTypeProxy(TypeProxy node)
        {
            if (node.ProxyFor == null) throw new NotImplementedException();
            ReturnResult(Translate(node.ProxyFor));
            return node;
        }

        //not implemented
        public override Type VisitType(Type type)
        {
            throw new NotImplementedException();
        }

        public override MapType VisitMapType(MapType node)
        {
            throw new NotImplementedException();
        }

        public override Type VisitBvType(BvType node)
        {
            throw new NotImplementedException();
        }

        public override Type VisitFloatType(FloatType node)
        {
            throw new NotImplementedException();
        }
    }
}