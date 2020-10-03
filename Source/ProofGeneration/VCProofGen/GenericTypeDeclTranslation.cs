using Microsoft.Boogie;
using ProofGeneration.Isa;
using ProofGeneration.Util;

namespace ProofGeneration.VCProofGen
{
    class GenericTypeDeclTranslation : VCTypeDeclTranslation
    {
        private readonly IsaUniqueNamer uniqueNamer;
        public GenericTypeDeclTranslation(IsaUniqueNamer uniqueNamer)
        {
            this.uniqueNamer = uniqueNamer;
        }
        
        public override Term Type(Function func)
        {
            return IsaCommonTerms.TermIdentFromName(uniqueNamer.GetName(func, func.Name));
        }

        public override Term Ctor(Function func)
        {
            return IsaCommonTerms.TermIdentFromName(uniqueNamer.GetName(func, func.Name));
        }

        public override Term IntType(Function func)
        {
            return IsaCommonTerms.TermIdentFromName(uniqueNamer.GetName(func, func.Name));
        }

        public override Term BoolType(Function func)
        {
            return IsaCommonTerms.TermIdentFromName(uniqueNamer.GetName(func, func.Name));
        }

        public override Term U2Int(Function func)
        {
            return IsaCommonTerms.TermIdentFromName(uniqueNamer.GetName(func, func.Name));
        }

        public override Term U2Bool(Function func)
        {
            return IsaCommonTerms.TermIdentFromName(uniqueNamer.GetName(func, func.Name));
        }

        public override Term Int2U(Function func)
        {
            return IsaCommonTerms.TermIdentFromName(uniqueNamer.GetName(func, func.Name));
        }

        public override Term Bool2U(Function func)
        {
            return IsaCommonTerms.TermIdentFromName(uniqueNamer.GetName(func, func.Name));
        }

        public override Term TypeConstructor(string constrName, Function func)
        {
            return IsaCommonTerms.TermIdentFromName(uniqueNamer.GetName(func, func.Name));
        }

        public override Term TypeConstructorInverse(string constrName, int index, Function func)
        {
            return IsaCommonTerms.TermIdentFromName(uniqueNamer.GetName(func, func.Name));
        }
    }
}