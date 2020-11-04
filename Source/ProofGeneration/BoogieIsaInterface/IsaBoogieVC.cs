using ProofGeneration.Isa;
using System;
using System.Collections.Generic;

namespace ProofGeneration.BoogieIsaInterface
{
    public static class IsaBoogieVC
    {
        public static TermIdent VCInvId { get; } = IsaCommonTerms.TermIdentFromName("vc_inv_closed");
        public static TermIdent VCTypeId { get; } = IsaCommonTerms.TermIdentFromName("vc_type_of_val");
        public static TermIdent TyToClosedId { get; } = IsaCommonTerms.TermIdentFromName("ty_to_closed");
        public static TermIdent ClosedToTyId { get; } = IsaCommonTerms.TermIdentFromName("closed_to_ty");
        public static TermIdent ValOfClosedTyId { get; } = IsaCommonTerms.TermIdentFromName("val_of_closed_type");

        private static TermIdent TPrimClosedId { get;  } = IsaCommonTerms.TermIdentFromName("TPrimC");
        
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
        
        public static TypeIsa BoogieClosedType()
        {
            return IsaCommonTypes.GetDataTypeNoArg("closed_ty");
        }
        
        public static Term PrimTypeClosed(Term primType)
        {
            return new TermApp(TPrimClosedId, primType);
        }

        public static Term TyToClosed(Term ty)
        {
            return new TermApp(TyToClosedId, ty);
        }

        public static Term ClosedToTy(Term ty)
        {
            return new TermApp(ClosedToTyId, ty);
        }

        public static Term ValOfClosedTy(Term absValTyMap, Term ty)
        {
            return new TermApp(ValOfClosedTyId, new List<Term>{ absValTyMap, ty });
        }

    }
}
