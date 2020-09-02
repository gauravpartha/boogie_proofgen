using ProofGeneration.Isa;
using System;

namespace ProofGeneration.BoogieIsaInterface
{
    public static class IsaBoogieVCTerm
    {
        public static TermIdent VCInvId { get; } = IsaCommonTerms.TermIdentFromName("vc_inv");
        public static TermIdent VCTypeId { get; } = IsaCommonTerms.TermIdentFromName("vc_val_to_type");

        public static Term VCInv(int idx)
        {
            return new TermApp(VCInvId, new NatConst(idx));
        }

        public static Term VCType(Term absValTyMap)
        {
            return new TermApp(VCTypeId, absValTyMap);
        }

        public static Term VCTypeConstructor(string constrName, int nArgs)
        {
            //TODO: do not limit number of arguments
            if(nArgs > 5)
            {
                throw new NotImplementedException("Do not support more than 5 type constructor arguments currently.");
            }

            var id = IsaCommonTerms.TermIdentFromName("vc_type_constr" + nArgs);
            return new TermApp(id, new StringConst(constrName));
        }

    }
}
