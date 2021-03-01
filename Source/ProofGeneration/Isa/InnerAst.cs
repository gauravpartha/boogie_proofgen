using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.BaseTypes;
using ProofGeneration.IsaPrettyPrint;

namespace ProofGeneration.Isa
{
    public abstract class Identifier
    {
    }

    public class SimpleIdentifier : Identifier
    {
        public readonly string name;

        public SimpleIdentifier(string name)
        {
            this.name = name;
        }

        public override string ToString()
        {
            return name;
        }
    }

    internal class Wildcard : Identifier
    {
    }

    #region Term

    public abstract class Term
    {
        public abstract T Dispatch<T>(TermVisitor<T> visitor);

        public override string ToString()
        {
            return new TermPrettyPrinter().Visit(this);
        }
    }

    public class TermIdent : Term
    {
        public readonly Identifier id;

        public TermIdent(Identifier id)
        {
            this.id = id;
        }

        public override T Dispatch<T>(TermVisitor<T> visitor)
        {
            return visitor.VisitTermIdent(this);
        }
    }

    public class TermApp : Term
    {
        public readonly IList<Term> arg; //technically don't require lists, but allows one to keep structure
        public readonly Term fun;

        public TermApp(Term fun, IList<Term> arg)
        {
            this.fun = fun;
            this.arg = arg;
        }

        public TermApp(Term fun, params Term[] args) : this(fun, args.ToList())
        {
        }

        public override T Dispatch<T>(TermVisitor<T> visitor)
        {
            return visitor.VisitTermApp(this);
        }
    }

    public class TermWithExplicitType : Term
    {
        public readonly Term term;
        public readonly TypeIsa type;

        public TermWithExplicitType(Term term, TypeIsa type)
        {
            this.term = term;
            this.type = type;
        }

        public override T Dispatch<T>(TermVisitor<T> visitor)
        {
            return visitor.VisitTermWithExplicitType(this);
        }
    }

    public class TermList : Term
    {
        public readonly IList<Term> list;

        public TermList(IList<Term> list)
        {
            this.list = list;
        }

        public override T Dispatch<T>(TermVisitor<T> visitor)
        {
            return visitor.VisitTermList(this);
        }
    }

    public class TermSet : Term
    {
        public readonly IEnumerable<Term> elements;

        public TermSet(IEnumerable<Term> elements)
        {
            this.elements = elements;
        }

        public override T Dispatch<T>(TermVisitor<T> visitor)
        {
            return visitor.VisitTermSet(this);
        }
    }

    public class TermTuple : Term
    {
        public readonly IList<Term> terms;

        public TermTuple(IList<Term> terms)
        {
            this.terms = terms;
        }

        public TermTuple(Term t1, Term t2) : this(new List<Term> {t1, t2})
        {
        }

        public override T Dispatch<T>(TermVisitor<T> visitor)
        {
            return visitor.VisitTermTuple(this);
        }
    }

    public class TermRecord : Term
    {
        public readonly IList<Tuple<string, Term>> mapping;

        public TermRecord(IList<Tuple<string, Term>> mapping)
        {
            this.mapping = mapping;
        }

        public override T Dispatch<T>(TermVisitor<T> visitor)
        {
            return visitor.VisitTermRecord(this);
        }
    }

    public class TermQuantifier : Term
    {
        public enum QuantifierKind
        {
            ALL,
            EX,
            META_ALL, //\<And>
            LAMBDA
        }

        public readonly IList<Identifier> boundVars;

        //if boundVarTypes is null, then types must be inferred, otherwise a type is provided for each bound variable
        public readonly IList<TypeIsa> boundVarTypes;

        public readonly QuantifierKind quantifier;
        public readonly Term term;

        //if boundVarTypes is null, then this represents not providing explicit types
        public TermQuantifier(QuantifierKind quantifier, IList<Identifier> boundVars, IList<TypeIsa> boundVarTypes,
            Term term)
        {
            if (boundVars == null || boundVarTypes != null && boundVars.Count != boundVarTypes.Count)
                throw new ArgumentException();
            this.quantifier = quantifier;
            this.boundVars = boundVars;
            this.boundVarTypes = boundVarTypes;
            this.term = term;
        }

        public TermQuantifier(QuantifierKind quantifier, IList<Identifier> boundVars, Term term) : this(quantifier,
            boundVars, null, term)
        {
        }

        public static TermQuantifier ForAll(IList<Identifier> boundVars, IList<TypeIsa> boundVarsTypes, Term term)
        {
            return new TermQuantifier(QuantifierKind.ALL, boundVars, boundVarsTypes, term);
        }

        public static TermQuantifier Exists(IList<Identifier> boundVars, IList<TypeIsa> boundVarsTypes, Term term)
        {
            return new TermQuantifier(QuantifierKind.EX, boundVars, boundVarsTypes, term);
        }

        public static TermQuantifier MetaAll(IList<Identifier> boundVars, IList<TypeIsa> boundVarsTypes, Term term)
        {
            return new TermQuantifier(QuantifierKind.META_ALL, boundVars, boundVarsTypes, term);
        }

        public static TermQuantifier Lambda(IList<Identifier> boundVars, IList<TypeIsa> boundVarsTypes, Term term)
        {
            return new TermQuantifier(QuantifierKind.LAMBDA, boundVars, boundVarsTypes, term);
        }

        public override T Dispatch<T>(TermVisitor<T> visitor)
        {
            return visitor.VisitTermQuantifier(this);
        }
    }

    public class TermCaseOf : Term
    {
        public readonly IEnumerable<Tuple<Term, Term>> matchCases;
        public readonly Term termToMatch;

        public TermCaseOf(Term termToMatch, IEnumerable<Tuple<Term, Term>> matchCases)
        {
            this.termToMatch = termToMatch;
            this.matchCases = matchCases;
        }

        public override T Dispatch<T>(TermVisitor<T> visitor)
        {
            return visitor.VisitTermCaseOf(this);
        }
    }

    public class TermBinary : Term
    {
        public enum BinaryOpCode
        {
            META_IMP, //\<Longrightarrow>
            EQ,
            NEQ,
            LT,
            LE,
            GT,
            GE,
            AND,
            OR,
            IMPLIES,
            ADD,
            SUB,
            MUL
        }

        public readonly Term argLeft;
        public readonly Term argRight;

        public readonly BinaryOpCode op;

        public TermBinary(Term argLeft, Term argRight, BinaryOpCode op)
        {
            this.argLeft = argLeft;
            this.argRight = argRight;
            this.op = op;
        }

        public static TermBinary Eq(Term argLeft, Term argRight)
        {
            return new TermBinary(argLeft, argRight, BinaryOpCode.EQ);
        }

        public static TermBinary Neq(Term argLeft, Term argRight)
        {
            return new TermBinary(argLeft, argRight, BinaryOpCode.NEQ);
        }

        public static TermBinary Le(Term argLeft, Term argRight)
        {
            return new TermBinary(argLeft, argRight, BinaryOpCode.LE);
        }

        public static TermBinary Ge(Term argLeft, Term argRight)
        {
            return new TermBinary(argLeft, argRight, BinaryOpCode.GE);
        }

        public static TermBinary And(Term argLeft, Term argRight)
        {
            return new TermBinary(argLeft, argRight, BinaryOpCode.AND);
        }

        public static TermBinary Implies(Term argLeft, Term argRight)
        {
            return new TermBinary(argLeft, argRight, BinaryOpCode.IMPLIES);
        }

        public static TermBinary MetaImplies(Term argLeft, Term argRight)
        {
            return new TermBinary(argLeft, argRight, BinaryOpCode.META_IMP);
        }

        public override T Dispatch<T>(TermVisitor<T> visitor)
        {
            return visitor.VisitTermBinary(this);
        }
    }

    public class TermUnary : Term
    {
        public enum UnaryOpCode
        {
            NOT
        }

        public readonly Term arg;

        public readonly UnaryOpCode op;

        public TermUnary(Term arg)
        {
            this.arg = arg;
        }

        public override T Dispatch<T>(TermVisitor<T> visitor)
        {
            return visitor.VisitTermUnary(this);
        }
    }

    public class BoolConst : Term
    {
        public readonly bool b;

        public BoolConst(bool b)
        {
            this.b = b;
        }

        public override T Dispatch<T>(TermVisitor<T> visitor)
        {
            return visitor.VisitBoolConst(this);
        }
    }

    public class NatConst : Term
    {
        public readonly int n;

        //if set to true, then the pretty printer will use "Suc" constructors to represent n and otherwise just decimal representation
        public readonly bool useConstructorRepr;

        public NatConst(int n, bool useConstructorRepr)
        {
            this.n = n;
            this.useConstructorRepr = useConstructorRepr;
        }

        public NatConst(int n)
        {
            this.n = n;
        }

        public override T Dispatch<T>(TermVisitor<T> visitor)
        {
            return visitor.VisitNatConst(this);
        }

        [ContractInvariantMethod]
        protected void ObjectInvariant()
        {
            Contract.Invariant(n >= 0);
        }
    }

    public class IntConst : Term
    {
        public readonly BigNum i;

        public IntConst(BigNum i)
        {
            this.i = i;
        }

        public IntConst(int i)
        {
            this.i = BigNum.FromInt(i);
        }

        public override T Dispatch<T>(TermVisitor<T> visitor)
        {
            return visitor.VisitIntConst(this);
        }
    }

    public class StringConst : Term
    {
        public readonly string s;

        public StringConst(string s)
        {
            this.s = s;
        }

        public override T Dispatch<T>(TermVisitor<T> visitor)
        {
            return visitor.VisitStringConst(this);
        }
    }

    #endregion

    #region Type

    public abstract class TypeIsa
    {
        public abstract T Dispatch<T>(TypeIsaVisitor<T> visitor);
    }

    public class VarType : TypeIsa
    {
        public readonly string name;

        public VarType(string name)
        {
            this.name = name;
        }

        public override T Dispatch<T>(TypeIsaVisitor<T> visitor)
        {
            return visitor.VisitVarType(this);
        }
    }

    public class ArrowType : TypeIsa
    {
        public readonly TypeIsa argType;
        public readonly TypeIsa resType;

        public ArrowType(TypeIsa argType, TypeIsa resType)
        {
            this.argType = argType;
            this.resType = resType;
        }

        public override T Dispatch<T>(TypeIsaVisitor<T> visitor)
        {
            return visitor.VisitArrowType(this);
        }
    }

    public class DataType : TypeIsa
    {
        public readonly IList<TypeIsa> args;
        public readonly string name;

        public DataType(string name, IList<TypeIsa> args)
        {
            this.name = name;
            this.args = args;
        }

        public DataType(string name, params TypeIsa[] args) : this(name, new List<TypeIsa>(args))
        {
        }

        public override T Dispatch<T>(TypeIsaVisitor<T> visitor)
        {
            return visitor.VisitDataType(this);
        }
    }

    public class TupleType : TypeIsa
    {
        public readonly IList<TypeIsa> args;

        public TupleType(IList<TypeIsa> args)
        {
            this.args = args;
        }

        public TupleType(params TypeIsa[] args) : this(new List<TypeIsa>(args))
        {
        }

        public override T Dispatch<T>(TypeIsaVisitor<T> visitor)
        {
            return visitor.VisitTupleType(this);
        }
    }

    public class SumType : TypeIsa
    {
        public readonly IList<TypeIsa> args;

        public SumType(IList<TypeIsa> args)
        {
            this.args = args;
        }

        public SumType(params TypeIsa[] args) : this(new List<TypeIsa>(args))
        {
        }

        public override T Dispatch<T>(TypeIsaVisitor<T> visitor)
        {
            return visitor.VisitSumType(this);
        }
    }

    public enum SimpleType
    {
        Bool,
        Nat,
        Int,
        String
    }

    public class PrimitiveType : TypeIsa
    {
        public readonly SimpleType simpleType;

        public PrimitiveType(SimpleType simpleType)
        {
            this.simpleType = simpleType;
        }

        public override T Dispatch<T>(TypeIsaVisitor<T> visitor)
        {
            return visitor.VisitPrimitiveType(this);
        }
    }

    #endregion
}