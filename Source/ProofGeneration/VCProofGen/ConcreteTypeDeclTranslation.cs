using System;
using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.Isa;

namespace ProofGeneration.VCProofGen
{
    class ConcreteTypeDeclTranslation : VCTypeDeclTranslation
    {

        private readonly BoogieContextIsa _boogieContextIsa;
        
        public ConcreteTypeDeclTranslation(BoogieContextIsa boogieContextIsa)
        {
            _boogieContextIsa = boogieContextIsa;
        }
        
        
        public override Term Ctor(Function func)
        {
            throw new NotImplementedException();
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
            return IsaBoogieType.PrimType(IsaBoogieType.BoolType());
        }

        public override Term IntType(Function func)
        {
            return IsaBoogieType.PrimType(IsaBoogieType.IntType());
        }

        public override Term Type(Function func)
        {
            return IsaBoogieVCTerm.VCType(_boogieContextIsa.absValTyMap);
        }

        public override Term TypeConstructor(string constrName, Function func)
        {
            return IsaBoogieVCTerm.VCTypeConstructor(constrName, func.InParams.Count);
        }

        public override Term TypeConstructorInverse(string constrName, int index, Function func)
        {
            return IsaBoogieVCTerm.VCInv(index);
        }
    }
}
