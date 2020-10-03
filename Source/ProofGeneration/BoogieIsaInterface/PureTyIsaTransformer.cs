using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using ProofGeneration.Isa;

namespace ProofGeneration.BoogieIsaInterface
{
    class PureTyIsaTransformer : ResultReadOnlyVisitor<TypeIsa>
    {
        //valueTy represents the Boogie values in the VC and typeTy represents the Boogie types in the VC
        private readonly TypeIsa valueTy;
        private readonly TypeIsa typeTy;


        public PureTyIsaTransformer(TypeIsa valueTy, TypeIsa typeTy)
        {
            this.valueTy = valueTy;
            this.typeTy = typeTy;
        }

        public PureTyIsaTransformer() : this(new VarType("u"), new VarType("t"))
        { }
        

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

            TypeIsa nonPolyType = types.Reverse().Aggregate((res, arg) => new ArrowType(arg, res));

            //need to add arguments for type parameters
            //TODO: for type guard approach only need t o add parameters for those parameters that cannot be extracted
            TypeIsa polyType = node.TypeParameters.Aggregate(nonPolyType, (res, arg) => new ArrowType(typeTy, res));

            ReturnResult(polyType);

            return node;
        }

        public override Microsoft.Boogie.Type VisitTypeVariable(TypeVariable node)
        {
            ReturnResult(valueTy);
            return node;
        }

        public override CtorType VisitCtorType(CtorType node)
        {
            //TODO: checking for T by name does not work in general, fix this by parametrizing the class by the actual object
            if(node.Decl.Name.Equals("T") && !node.Arguments.Any())
            {
                ReturnResult(typeTy);
            } else
            {
                //we don't support VC optimizations that monomorphize the VC if there are no polymorphic types for now
                //hence values of a type generated via a constructor are always represented by u
                ReturnResult(valueTy);
            }

            return node;
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
               //TODO: just returning some type so that can test, but need to adjust this
               ReturnResult(new PrimitiveType(Isa.SimpleType.Int));
            }

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
