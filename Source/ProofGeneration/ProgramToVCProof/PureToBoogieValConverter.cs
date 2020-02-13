using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using Microsoft.Boogie;
using ProofGeneration.Isa;

namespace ProofGeneration.ProgramToVCProof
{
    class PureToBoogieValConverter : ResultReadOnlyVisitor<Func<Term, Term>>
    {

        public Term ConvertToBoogieVal(Microsoft.Boogie.Type ty, Term pureVal)
        {
            return this.Translate(ty)(pureVal);
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
            if (node.IsBool)
            {
                ReturnResult(v => IsaBoogieTerm.BoolVal(v));
            }
            else if (node.IsInt)
            {
                ReturnResult(v => IsaBoogieTerm.IntVal(v));
            }
            else
            {
                throw new NotImplementedException();
            }

            return node;
        }
    }
}
