using System;
using System.Diagnostics.Contracts;
using System.Linq;
using Isabelle.Ast;
using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface.VariableTranslation;
using Type = Microsoft.Boogie.Type;

namespace ProofGeneration
{
    public class TypeIsaVisitor : ResultReadOnlyVisitor<Term>
    {
        private readonly IVariableTranslation<TypeVariable> typeVarTranslation;
        private readonly bool usedClosedConstructors;

        public TypeIsaVisitor(IVariableTranslation<TypeVariable> typeVarTranslation,
            bool usedClosedConstructors = false)
        {
            this.typeVarTranslation = typeVarTranslation;
            this.usedClosedConstructors = usedClosedConstructors;
        }

        [ContractInvariantMethod]
        private void ObjectInvariant()
        {
            Contract.Invariant(Results != null);
            Contract.Invariant(Results.Count <= 1);
        }


        protected override bool TranslatePrecondition(Absy node)
        {
            return node is Type;
        }
        
        public override Type VisitTypeVariable(TypeVariable node)
        {
            ReturnResult(typeVarTranslation.TranslateVariable(node, out _));
            return node;
        }

        public override CtorType VisitCtorType(CtorType node)
        {
            var argTypes = node.Arguments.Select(t => Translate(t)).ToList();

            ReturnResult(IsaBoogieType.TConType(node.Decl.Name, argTypes, usedClosedConstructors));
            return node;
        }

        public override Type VisitBasicType(BasicType node)
        {
            if (node.IsBool)
                ReturnResult(IsaBoogieType.PrimType(IsaBoogieType.BoolType(), usedClosedConstructors));
            else if (node.IsInt)
                ReturnResult(IsaBoogieType.PrimType(IsaBoogieType.IntType(), usedClosedConstructors));
            else if (node.IsReal)
                ReturnResult(IsaBoogieType.PrimType(IsaBoogieType.RealType(), usedClosedConstructors));
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

        public override Type VisitTypeSynonymAnnotation(TypeSynonymAnnotation node)
        {
            ReturnResult(Translate(node.ExpandedType));
            //ignoring arguments
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