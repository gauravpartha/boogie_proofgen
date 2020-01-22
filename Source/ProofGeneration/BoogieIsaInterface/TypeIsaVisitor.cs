using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using Microsoft.Boogie;

namespace ProofGeneration
{
    class TypeIsaVisitor : ResultReadOnlyVisitor<Term>
    {
        [ContractInvariantMethod]
        void ObjectInvariant()
        {
            Contract.Invariant(Results != null);
            Contract.Invariant(Results.Count <= 1);
        }

        protected override bool TranslatePrecondition(Absy node)
        {
            return node is Microsoft.Boogie.Type;
        }

        public override Microsoft.Boogie.Type VisitType(Microsoft.Boogie.Type type)
        {
            throw new NotImplementedException();
        }

        public override Microsoft.Boogie.Type VisitBasicType(BasicType node)
        {
            if(node.IsBool)
            {
                ReturnResult(IsaBoogieType.BoolType());
            } else if(node.IsInt)
            {
                ReturnResult(IsaBoogieType.IntType());
            } else
            {
                throw new NotImplementedException();
            }

            return node;
        }

    }
}
