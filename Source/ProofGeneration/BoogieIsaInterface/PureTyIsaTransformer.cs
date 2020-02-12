using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using Microsoft.Boogie;
using ProofGeneration.Isa;

namespace ProofGeneration.VCProofGen
{
    class PureTyIsaTransformer : ResultReadOnlyVisitor<TypeIsa>
    {
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
