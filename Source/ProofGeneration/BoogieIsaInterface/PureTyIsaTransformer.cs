using System;
using System.Collections.Generic;
using System.Linq;
using Isabelle.Ast;
using Microsoft.Boogie;
using Type = Microsoft.Boogie.Type;

namespace ProofGeneration.BoogieIsaInterface
{
    internal class PureTyIsaTransformer : ResultReadOnlyVisitor<TypeIsa>
    {
        private readonly TypeIsa typeTy;

        //valueTy represents the Boogie values in the VC and typeTy represents the Boogie types in the VC
        private readonly TypeIsa valueTy;


        public PureTyIsaTransformer(TypeIsa valueTy, TypeIsa typeTy)
        {
            this.valueTy = valueTy;
            this.typeTy = typeTy;
        }

        public PureTyIsaTransformer() : this(new VarType("u"), new VarType("t"))
        {
        }


        protected override bool TranslatePrecondition(Absy node)
        {
            return node is GlobalVariable ||
                   node is Constant ||
                   node is LocalVariable ||
                   node is Formal ||
                   node is Function ||
                   node is Type;
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

        public override Constant VisitConstant(Constant node)
        {
            return (Constant) VisitVariable(node);
        }

        public override GlobalVariable VisitGlobalVariable(GlobalVariable node)
        {
            return (GlobalVariable) VisitVariable(node);
        }

        public override Function VisitFunction(Function node)
        {
            IList<TypeIsa> types = node.InParams.Select(v => Translate(v.TypedIdent.Type)).ToList();

            var retType = Translate(node.OutParams[0].TypedIdent.Type);
            types.Add(retType);

            var nonPolyType = types.Reverse().Aggregate((res, arg) => new ArrowType(arg, res));

            //need to add arguments for type parameters
            //TODO: for type guard approach only need t o add parameters for those parameters that cannot be extracted
            var polyType = node.TypeParameters.Aggregate(nonPolyType, (res, arg) => new ArrowType(typeTy, res));

            ReturnResult(polyType);

            return node;
        }

        public override Type VisitTypeVariable(TypeVariable node)
        {
            ReturnResult(valueTy);
            return node;
        }

        public override CtorType VisitCtorType(CtorType node)
        {
            //TODO: checking for T by name does not work in general, fix this by parametrizing the class by the actual object
            if (node.Decl.Name.Equals("T") && !node.Arguments.Any())
                ReturnResult(typeTy);
            else
                //we don't support VC optimizations that monomorphize the VC if there are no polymorphic types for now
                //hence values of a type generated via a constructor are always represented by u
                ReturnResult(valueTy);

            return node;
        }

        public override Type VisitBasicType(BasicType node)
        {
            if (node.IsBool)
                ReturnResult(PrimitiveType.CreateBoolType());
            else if (node.IsInt)
                ReturnResult(PrimitiveType.CreateIntType());
            else
                throw new ProofGenUnexpectedStateException("unexpected pure basic type");

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