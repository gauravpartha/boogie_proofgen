using Isabelle.Ast;
using Isabelle.Util;
using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface;

namespace ProofGeneration.VCProofGen
{
    internal class ConcreteTypeDeclTranslation : VCTypeDeclTranslation
    {
        private readonly BoogieContextIsa _boogieContextIsa;

        public ConcreteTypeDeclTranslation(BoogieContextIsa boogieContextIsa)
        {
            _boogieContextIsa = boogieContextIsa;
        }


        public override Term Ctor(Function func)
        {
            //TODO just returning something here
            return IsaCommonTerms.TermIdentFromName("Ctor");
        }

        public override Term Bool2U(Function func)
        {
            return IsaBoogieTerm.BoolValConstr();
        }

        public override Term Int2U(Function func)
        {
            return IsaBoogieTerm.IntValConstr();
        }

        public override Term U2Bool(Function func)
        {
            return IsaBoogieTerm.ConvertValToBoolId;
        }

        public override Term U2Int(Function func)
        {
            return IsaBoogieTerm.ConvertValToIntId;
        }

        public override Term BoolType(Function func)
        {
            return IsaBoogieVC.PrimTypeClosed(IsaBoogieType.BoolType());
        }

        public override Term IntType(Function func)
        {
            return IsaBoogieVC.PrimTypeClosed(IsaBoogieType.IntType());
        }

        public override Term Type(Function func)
        {
            return IsaBoogieVC.VCType(_boogieContextIsa.absValTyMap);
        }

        public override Term TypeConstructor(string constrName, Function func)
        {
            return IsaBoogieVC.VCTypeConstructor(constrName, func.InParams.Count);
        }

        public override Term TypeConstructorInverse(string constrName, int index, Function func)
        {
            return IsaBoogieVC.VCInv(index);
        }
    }
}