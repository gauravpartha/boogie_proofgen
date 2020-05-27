using System.Diagnostics.Contracts;

namespace ProofGeneration.VCProofGen
{
    public abstract class VCHint
    {
        public abstract string GetMLRepr();

        public override string ToString()
        {
            return GetMLRepr();
        }
    }

    public class AssumeConjHint : VCHint
    {
        public int NestLevel { get; set; }        

        //top level conjunctions
        public int NumConjunctions { get; }
        
        //total number of commands in this conjunct, -1 is unknown
        public int NumCommands { get; set; }

        public AssumeConjHint(int nestLevel, int numConjunctions, int numCommands)
        {
            Contract.Requires(nestLevel > 0);
            NestLevel = nestLevel;
            NumConjunctions = numConjunctions;
            NumCommands = numCommands;
        }

        public override string GetMLRepr()
        {
            return "AssumeConjR " + NestLevel;
        }
    }

    public class AssertSimpleHint : VCHint
    {
        public readonly AssertSimpleType hintType;

        public enum AssertSimpleType { CONJ, NO_CONJ, SUBSUMPTION }

        public AssertSimpleHint(AssertSimpleType hintType)
        {
            this.hintType = hintType;
        }

        public override string GetMLRepr()
        {
            switch (hintType)
            {
                case AssertSimpleType.CONJ: return "AssertConj";
                case AssertSimpleType.NO_CONJ: return "AssertNoConj";
                case AssertSimpleType.SUBSUMPTION: return "AssertSub";
                default: throw new ProofGenUnexpectedStateException(GetType(), "unexpected assert simple hint type");
            }
        }
    }
}
