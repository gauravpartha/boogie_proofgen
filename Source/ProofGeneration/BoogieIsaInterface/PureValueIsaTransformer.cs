using System;
using Microsoft.Boogie;
using ProofGeneration.Isa;

namespace ProofGeneration.BoogieIsaInterface
{
    class PureValueIsaTransformer : ResultReadOnlyVisitor<Term>
    {

        private Term arg;
        private bool constructVal;

        protected override bool TranslatePrecondition(Absy node)
        {
            return node is Microsoft.Boogie.Type;
        }

        public Term ConstructValue(Term pureArg, Microsoft.Boogie.Type boogieType)
        {
            arg = pureArg;
            constructVal = true;
            return Translate(boogieType);
        }

        public Term DestructValue(Term boogieValue, Microsoft.Boogie.Type boogieType)
        {
            arg = boogieValue;
            constructVal = false;
            return Translate(boogieType);
        }

        public override Microsoft.Boogie.Type VisitType(Microsoft.Boogie.Type type)
        {
            throw new NotImplementedException();
        }

        public override Microsoft.Boogie.Type VisitBasicType(BasicType node)
        {
            if (node.IsBool)
            {
                if(constructVal)
                {
                    ReturnResult(IsaBoogieTerm.BoolVal(arg));
                } else
                {
                    ReturnResult(IsaBoogieTerm.ConvertValToBool(arg));
                }
            }
            else if (node.IsInt)
            {
                if(constructVal)
                {
                    ReturnResult(IsaBoogieTerm.IntVal(arg));
                } else
                {
                    ReturnResult(IsaBoogieTerm.ConvertValToInt(arg));
                }
            }
            else
            {
                throw new NotImplementedException();
            }

            return node;
        }
        public override Microsoft.Boogie.Type VisitTypeVariable(TypeVariable node)
        {
            ReturnResult(arg);
            return node;
        }

        public override CtorType VisitCtorType(CtorType node)
        {
            ReturnResult(arg);
            return node;
        }
    }
}
