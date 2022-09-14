using System;
using Isabelle.Ast;
using Microsoft.Boogie;
using Type = Microsoft.Boogie.Type;

namespace ProofGeneration.BoogieIsaInterface
{
    internal class PureValueIsaTransformer : ResultReadOnlyVisitor<Term>
    {
        private Term arg;
        private bool constructVal;

        protected override bool TranslatePrecondition(Absy node)
        {
            return node is Type;
        }

        public Term ConstructValue(Term pureArg, Type boogieType)
        {
            arg = pureArg;
            constructVal = true;
            return Translate(boogieType);
        }

        public Term DestructValue(Term boogieValue, Type boogieType)
        {
            arg = boogieValue;
            constructVal = false;
            return Translate(boogieType);
        }

        public override Type VisitType(Type type)
        {
            throw new NotImplementedException();
        }

        public override Type VisitBasicType(BasicType node)
        {
            if (node.IsBool)
            {
                if (constructVal)
                    ReturnResult(IsaBoogieTerm.BoolVal(arg));
                else
                    ReturnResult(IsaBoogieTerm.ConvertValToBool(arg));
            }
            else if (node.IsInt)
            {
                if (constructVal)
                    ReturnResult(IsaBoogieTerm.IntVal(arg));
                else
                    ReturnResult(IsaBoogieTerm.ConvertValToInt(arg));
            } 
            else if (node.IsReal)
            {
                if (constructVal)    
                    ReturnResult(IsaBoogieTerm.RealVal(arg));
                else
                    ReturnResult(IsaBoogieTerm.ConvertValToReal(arg));
            }
            else
            {
                throw new NotImplementedException();
            }

            return node;
        }

        public override Type VisitTypeVariable(TypeVariable node)
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