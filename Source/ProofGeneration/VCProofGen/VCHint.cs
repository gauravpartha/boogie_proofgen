using System.Diagnostics.Contracts;
using Isabelle.ML;

namespace ProofGeneration.VCProofGen
{
    public abstract class VCHint : INodeML
    {
        public VCHint(VCExprHint exprHint)
        {
            ExprHint = exprHint;
        }

        //hint used to prove relationship between vc expression and Boogie expression in Assume/Assert statement
        public VCExprHint ExprHint { get; }

        public string GetMLString()
        {
            return "(" + VCHintMLRepr() + "," + ExprHint.GetMLString() + ")";
        }

        public abstract string VCHintMLRepr();

        /// <summary>
        ///     returns whether the hint is supposed to be enough to solve the vc block lemma completely
        /// </summary>
        public virtual bool IsFinal()
        {
            return false;
        }

        public override string ToString()
        {
            return GetMLString();
        }
    }

    public class AssumeSimpleHint : VCHint
    {
        public enum AssumeSimpleType
        {
            ASSUME_TRUE,
            ASSUME_FALSE,
            ASSUME_NOT
        }

        public readonly AssumeSimpleType hintType;

        public AssumeSimpleHint(AssumeSimpleType hintType, VCExprHint exprHint) : base(exprHint)
        {
            this.hintType = hintType;
        }

        public AssumeSimpleHint(AssumeSimpleType hintType) : this(hintType, VCExprHint.EmptyExprHint())
        {
        }

        public override string VCHintMLRepr()
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
        public AssumeConjHint(int nestLevel, int numConjunctions, int numCommands, VCExprHint vcExprHint) : base(
            vcExprHint)
        {
            Contract.Requires(nestLevel > 0);
            NestLevel = nestLevel;
            NumConjunctions = numConjunctions;
            NumCommands = numCommands;
        }

        public AssumeConjHint(int nestLevel, int numConjunctions, int numCommands) :
            this(nestLevel, numConjunctions, numCommands, VCExprHint.EmptyExprHint())
        {
        }

        public int NestLevel { get; set; }

        //top level conjunctions
        public int NumConjunctions { get; }

        //total number of commands in this conjunct, -1 is unknown
        public int NumCommands { get; set; }

        public override string VCHintMLRepr()
        {
            return "AssumeConjR " + NestLevel;
        }
    }

    public class AssertSimpleHint : VCHint
    {
        public enum AssertSimpleType
        {
            CONJ,
            NO_CONJ,
            SUBSUMPTION,
            ASSERT_TRUE,
            ASSERT_FALSE
        }

        public readonly AssertSimpleType hintType;

        public AssertSimpleHint(AssertSimpleType hintType, VCExprHint vcExprHint) : base(vcExprHint)
        {
            this.hintType = hintType;
        }

        public AssertSimpleHint(AssertSimpleType hintType) : this(hintType, VCExprHint.EmptyExprHint())
        {
        }

        public override bool IsFinal()
        {
            switch (hintType)
            {
                case AssertSimpleType.ASSERT_FALSE: return true;
                default: return false;
            }
        }

        public override string VCHintMLRepr()
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