using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using ProofGeneration.Isa;

namespace ProofGeneration.BoogieIsaInterface
{
    class PureTyIsaTransformer : ResultReadOnlyVisitor<TypeIsa>
    {
        protected override bool TranslatePrecondition(Absy node)
        {
            return node is GlobalVariable ||
                node is LocalVariable ||
                node is Formal ||
                node is Function || 
                node is Microsoft.Boogie.Type;
        }

        public override Variable VisitVariable(Variable node)
        {
            Visit(node.TypedIdent.Type);
            return node;
        }

        public override Formal VisitFormal(Formal node)
        {
            return (Formal) VisitVariable(node);
        }

        public override LocalVariable VisitLocalVariable(LocalVariable node)
        {
            return (LocalVariable) VisitVariable(node); 
        }

        public override Function VisitFunction(Function node)
        {
            IList<TypeIsa> types = node.InParams.Select(v => Translate(v.TypedIdent.Type)).ToList();

            TypeIsa retType = Translate(node.OutParams[0].TypedIdent.Type);
            types.Add(retType);

            ReturnResult(types.Reverse().Aggregate((res, arg) => new ArrowType(arg, res)));

            return node;
        }

        public override Microsoft.Boogie.Type VisitType(Microsoft.Boogie.Type type)
        {
            throw new NotImplementedException();
        }

        public override Microsoft.Boogie.Type VisitBasicType(BasicType node)
        {
            if (node.IsBool)
            {
                ReturnResult(new PrimitiveType(Isa.SimpleType.Bool));
            }
            else if (node.IsInt)
            {
                ReturnResult(new PrimitiveType(Isa.SimpleType.Int));
            }
            else
            {
                throw new NotImplementedException();
            }

            return node;
        }

    }
}
