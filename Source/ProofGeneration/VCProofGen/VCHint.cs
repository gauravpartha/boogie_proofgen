using System.Diagnostics.Contracts;

namespace ProofGeneration.VCProofGen
{
    public abstract class VCHint
    {
        public abstract string GetMLRepr();

        /// <summary>
        /// returns whether the hint is supposed to be enough to solve the vc block lemma completely
        /// </summary>
        public virtual bool IsFinal()
        {
            return false;
        }

        public override string ToString()
        {
            return GetMLRepr();
        }
    }

    public class AssumeSimpleHint : VCHint
    {
        public readonly AssumeSimpleType hintType;

        public enum AssumeSimpleType { ASSUME_TRUE, ASSUME_FALSE, ASSUME_NOT }

        public AssumeSimpleHint(AssumeSimpleType hintType)
        {
            this.hintType = hintType;
        }

        public override string GetMLRepr()
        {
            switch (hintType)
            {
                case AssumeSimpleType.ASSUME_TRUE: return "AssumeTrue";
                case AssumeSimpleType.ASSUME_FALSE: return "AssumeFalse";
                case AssumeSimpleType.ASSUME_NOT: return "AssumeNot";
                default: throw new ProofGenUnexpectedStateException(GetType(), "unexpected assume simple hint type");
            }
        }

        public override bool IsFinal()
        {
            switch (hintType)
            {
                case AssumeSimpleType.ASSUME_FALSE: return true;
                case AssumeSimpleType.ASSUME_NOT: return true;
                default: return false;
            }
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

        public enum AssertSimpleType { CONJ, NO_CONJ, SUBSUMPTION, ASSERT_TRUE, ASSERT_FALSE }

        public AssertSimpleHint(AssertSimpleType hintType)
        {
            this.hintType = hintType;
        }

        public override bool IsFinal()
        {
            switch (hintType)
            {
                case AssertSimpleType.ASSERT_FALSE: return true;
                default: return false;
            }
        }

        public override string GetMLRepr()
        {
            switch (hintType)
            {
                case AssertSimpleType.CONJ: return "AssertConj";
                case AssertSimpleType.NO_CONJ: return "AssertNoConj";
                case AssertSimpleType.SUBSUMPTION: return "AssertSub";
                case AssertSimpleType.ASSERT_TRUE: return "AssertTrue";
                case AssertSimpleType.ASSERT_FALSE: return "AssertFalse";
                default: throw new ProofGenUnexpectedStateException(GetType(), "unexpected assert simple hint type");
            }
        }
    }
}
