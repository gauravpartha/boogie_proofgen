using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using Microsoft.Boogie;
using ProofGeneration.Isa;

namespace ProofGeneration.ProgramToVCProof
{
    class PureToBoogieValConverter : ResultReadOnlyVisitor<Func<Term, Term>>
    {

        public Term ConvertToBoogieVal(Microsoft.Boogie.Type ty, Term pureVal)
        {
            return this.Translate(ty)(pureVal);
        }

        protected override bool TranslatePrecondition(Absy node)
        {
            return node is Microsoft.Boogie.Type;
        }

        public override Microsoft.Boogie.Type VisitTypeVariable(TypeVariable node)
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

        public override Microsoft.Boogie.Type VisitBasicType(BasicType node)
        {
            if (node.IsBool)
            {
                ReturnResult(v => IsaBoogieTerm.BoolVal(v));
            }
            else if (node.IsInt)
            {
                ReturnResult(v => IsaBoogieTerm.IntVal(v));
            }
            else
            {
                throw new NotImplementedException();
            }

            return node;
        }

        public override Microsoft.Boogie.Type VisitTypeProxy(TypeProxy node)
        {
            if (node.ProxyFor == null)
            {
                throw new NotImplementedException();
            }
            ReturnResult(Translate(node.ProxyFor));
            return node;
        }

        //not implemented
        public override Microsoft.Boogie.Type VisitType(Microsoft.Boogie.Type type)
        {
            throw new NotImplementedException();
        }

        public override MapType VisitMapType(MapType node)
        {
            throw new NotImplementedException();
        }

        public override Microsoft.Boogie.Type VisitBvType(BvType node)
        {
            throw new NotImplementedException();
        }

        public override Microsoft.Boogie.Type VisitFloatType(FloatType node)
        {
            throw new NotImplementedException();
        }

    }
}
