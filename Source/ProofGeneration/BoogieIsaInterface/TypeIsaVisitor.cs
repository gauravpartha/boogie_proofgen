using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.BoogieIsaInterface.VariableTranslation;
using ProofGeneration.Isa;

namespace ProofGeneration
{
    public class TypeIsaVisitor : ResultReadOnlyVisitor<Term>
    {

        private readonly IVariableTranslation<TypeVariable> typeVarTranslation;
        private readonly bool usedClosedConstructors;

        [ContractInvariantMethod]
        void ObjectInvariant()
        {
            Contract.Invariant(Results != null);
            Contract.Invariant(Results.Count <= 1);
        }
        
        public TypeIsaVisitor(IVariableTranslation<TypeVariable> typeVarTranslation, bool usedClosedConstructors = false)
        {
            this.typeVarTranslation = typeVarTranslation;
            this.usedClosedConstructors = usedClosedConstructors;
        }


        protected override bool TranslatePrecondition(Absy node)
        {
            return node is Microsoft.Boogie.Type;
        }

        public override Microsoft.Boogie.Type VisitTypeVariable(TypeVariable node)
        {
            ReturnResult(typeVarTranslation.TranslateVariable(node));
            return node;
        }

        public override CtorType VisitCtorType(CtorType node)
        {
            List<Term> argTypes = node.Arguments.Select(t => Translate(t)).ToList();

            ReturnResult(IsaBoogieType.TConType(node.Decl.Name, argTypes, usedClosedConstructors));
            return node;
        }

        public override Microsoft.Boogie.Type VisitBasicType(BasicType node)
        {
            if(node.IsBool)
            {
                ReturnResult(IsaBoogieType.PrimType(IsaBoogieType.BoolType(), usedClosedConstructors));
            } else if(node.IsInt)
            {
                ReturnResult(IsaBoogieType.PrimType(IsaBoogieType.IntType(), usedClosedConstructors));
            } else
            {
                throw new NotImplementedException();
            }

            return node;
        }

        public override Microsoft.Boogie.Type VisitTypeProxy(TypeProxy node)
        {
            if(node.ProxyFor == null)
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
