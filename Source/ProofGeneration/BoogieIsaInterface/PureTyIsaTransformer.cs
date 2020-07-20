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
            return node is NamedDeclaration || node is Microsoft.Boogie.Type;
        }

        public TypeIsa TranslateDeclType(NamedDeclaration nd)
        {
            if (nd is Variable v)
                return TranslateBoogieVarType(v);
            else if (nd is Function f)
                return TranslateBoogieFunctionType(f);
            else
                throw new NotImplementedException();
        }

        private TypeIsa TranslateBoogieVarType(Variable v)
        {
            return Translate(v.TypedIdent.Type);
        }

        private TypeIsa TranslateBoogieFunctionType(Function fun)
        {
            IList<TypeIsa> types = fun.InParams.Select(v => Translate(v.TypedIdent.Type)).ToList();

            TypeIsa retType = Translate(fun.OutParams[0].TypedIdent.Type);
            types.Add(retType);

            return types.Reverse().Aggregate((res, arg) => new ArrowType(arg, res));
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
