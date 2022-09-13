using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Isabelle.IsaPrettyPrint;
using Microsoft.BaseTypes;

namespace Isabelle.Ast
{
    public abstract class Identifier
    {
    }

    public class SimpleIdentifier : Identifier
    {
        public SimpleIdentifier(string name)
        {
            Name = name;
        }

        public string Name { get; }

        public override string ToString()
        {
            return Name;
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
        public TermIdent(Identifier id)
        {
            Id = id;
        }

        public Identifier Id { get; }

        public override T Dispatch<T>(TermVisitor<T> visitor)
        {
            return visitor.VisitTermIdent(this);
        }
    }

    public class TermApp : Term
    {
        public TermApp(Term fun, IList<Term> arg)
        {
            Fun = fun;
            Arg = arg;
        }

        public TermApp(Term fun, params Term[] args) : this(fun, args.ToList())
        {
        }

        public IList<Term> Arg { get; }
        public Term Fun { get; }

        public override T Dispatch<T>(TermVisitor<T> visitor)
        {
            return visitor.VisitTermApp(this);
        }
    }

    public class TermWithExplicitType : Term
    {
        public TermWithExplicitType(Term term, TypeIsa type)
        {
            Term = term;
            Type = type;
        }

        public Term Term { get; }
        public TypeIsa Type { get; }

        public override T Dispatch<T>(TermVisitor<T> visitor)
        {
            return visitor.VisitTermWithExplicitType(this);
        }
    }

    public class TermList : Term
    {
        public TermList(IList<Term> list)
        {
            List = list;
        }

        public IList<Term> List { get; }

        public override T Dispatch<T>(TermVisitor<T> visitor)
        {
            return visitor.VisitTermList(this);
        }
    }

    public class TermSet : Term
    {
        public TermSet(IEnumerable<Term> elements)
        {
            Elements = elements;
        }

        public IEnumerable<Term> Elements { get; }

        public override T Dispatch<T>(TermVisitor<T> visitor)
        {
            return visitor.VisitTermSet(this);
        }
    }

    public class TermTuple : Term
    {
        public IList<Term> Terms;

        public TermTuple(IList<Term> terms)
        {
            Terms = terms;
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
        public TermRecord(IList<Tuple<string, Term>> mapping)
        {
            Mapping = mapping;
        }

        public IList<Tuple<string, Term>> Mapping { get; }

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

        //if boundVarTypes is null, then this represents not providing explicit types
        public TermQuantifier(QuantifierKind quantifier, IList<Identifier> boundVars, IList<TypeIsa> boundVarTypes,
            Term term)
        {
            if (boundVars == null || boundVarTypes != null && boundVars.Count != boundVarTypes.Count)
                throw new ArgumentException();
            Quantifier = quantifier;
            BoundVars = boundVars;
            BoundVarTypes = boundVarTypes;
            Term = term;
        }

        public TermQuantifier(QuantifierKind quantifier, IList<Identifier> boundVars, Term term) : this(quantifier,
            boundVars, null, term)
        {
        }

        public IList<Identifier> BoundVars { get; }

        //if boundVarTypes is null, then types must be inferred, otherwise a type is provided for each bound variable
        public IList<TypeIsa> BoundVarTypes { get; }

        public QuantifierKind Quantifier { get; }
        public Term Term { get; }

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
        public TermCaseOf(Term termToMatch, IEnumerable<Tuple<Term, Term>> matchCases)
        {
            TermToMatch = termToMatch;
            MatchCases = matchCases;
        }

        public IEnumerable<Tuple<Term, Term>> MatchCases { get; }
        public Term TermToMatch { get; }

        public override T Dispatch<T>(TermVisitor<T> visitor)
        {
            return visitor.VisitTermCaseOf(this);
        }
    }

    public class TermBinary : Term
    {
        public enum BinaryOpCode
        {
            MetaImp, //\<Longrightarrow>
            Eq,
            Neq,
            Lt,
            Le,
            Gt,
            Ge,
            And,
            Or,
            Implies,
            Add,
            Sub,
            Mul
        }

        public TermBinary(Term argLeft, Term argRight, BinaryOpCode op)
        {
            ArgLeft = argLeft;
            ArgRight = argRight;
            Op = op;
        }

        public Term ArgLeft { get; }
        public Term ArgRight { get; }

        public BinaryOpCode Op { get; }

        public static TermBinary Eq(Term argLeft, Term argRight)
        {
            return new TermBinary(argLeft, argRight, BinaryOpCode.Eq);
        }

        public static TermBinary Neq(Term argLeft, Term argRight)
        {
            return new TermBinary(argLeft, argRight, BinaryOpCode.Neq);
        }

        public static TermBinary Le(Term argLeft, Term argRight)
        {
            return new TermBinary(argLeft, argRight, BinaryOpCode.Le);
        }

        public static TermBinary Ge(Term argLeft, Term argRight)
        {
            return new TermBinary(argLeft, argRight, BinaryOpCode.Ge);
        }

        public static TermBinary And(Term argLeft, Term argRight)
        {
            return new TermBinary(argLeft, argRight, BinaryOpCode.And);
        }

        public static TermBinary Implies(Term argLeft, Term argRight)
        {
            return new TermBinary(argLeft, argRight, BinaryOpCode.Implies);
        }

        public static TermBinary MetaImplies(Term argLeft, Term argRight)
        {
            return new TermBinary(argLeft, argRight, BinaryOpCode.MetaImp);
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
            Not
        }

        public TermUnary(Term arg, UnaryOpCode op)
        {
            Arg = arg;
            Op = op;
        }

        public Term Arg { get; }

        public UnaryOpCode Op { get; }

        public override T Dispatch<T>(TermVisitor<T> visitor)
        {
            return visitor.VisitTermUnary(this);
        }
    }

    public class BoolConst : Term
    {
        public BoolConst(bool val)
        {
            Val = val;
        }

        public bool Val { get; }

        public override T Dispatch<T>(TermVisitor<T> visitor)
        {
            return visitor.VisitBoolConst(this);
        }
    }

    public class NatConst : Term
    {
        public NatConst(int val, bool useConstructorRepr)
        {
            Val = val;
            UseConstructorRepr = useConstructorRepr;
        }

        public NatConst(int val)
        {
            Val = val;
        }

        public int Val { get; }

        //if set to true, then the pretty printer will use "Suc" constructors to represent n and otherwise just decimal representation
        public bool UseConstructorRepr { get; }

        public override T Dispatch<T>(TermVisitor<T> visitor)
        {
            return visitor.VisitNatConst(this);
        }

        [ContractInvariantMethod]
        protected void ObjectInvariant()
        {
            Contract.Invariant(Val >= 0);
        }
    }

    public class IntConst : Term
    {
        public IntConst(BigNum val)
        {
            Val = val;
        }

        public IntConst(int val)
        {
            Val = BigNum.FromInt(val);
        }

        public BigNum Val { get; }

        public override T Dispatch<T>(TermVisitor<T> visitor)
        {
            return visitor.VisitIntConst(this);
        }
    }

    public class RealConst : Term
    {
        public RealConst(BigDec val)
        {
            Val = val;
        }
        
        public BigDec Val { get; }

        public override T Dispatch<T>(TermVisitor<T> visitor)
        {
            return visitor.VisitRealConst(this);
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
        public VarType(string name)
        {
            Name = name;
        }

        public string Name { get; }

        public override T Dispatch<T>(TypeIsaVisitor<T> visitor)
        {
            return visitor.VisitVarType(this);
        }
    }

    public class ArrowType : TypeIsa
    {
        public ArrowType(TypeIsa argType, TypeIsa resType)
        {
            ArgType = argType;
            ResType = resType;
        }

        public TypeIsa ArgType { get; }
        public TypeIsa ResType { get; }

        public override T Dispatch<T>(TypeIsaVisitor<T> visitor)
        {
            return visitor.VisitArrowType(this);
        }
    }

    public class DataType : TypeIsa
    {
        public DataType(string name, IList<TypeIsa> args)
        {
            Name = name;
            Args = args;
        }

        public DataType(string name, params TypeIsa[] args) : this(name, new List<TypeIsa>(args))
        {
        }

        public IList<TypeIsa> Args { get; }
        public string Name { get; }

        public override T Dispatch<T>(TypeIsaVisitor<T> visitor)
        {
            return visitor.VisitDataType(this);
        }
    }

    public class TupleType : TypeIsa
    {
        public TupleType(IList<TypeIsa> args)
        {
            Args = args;
        }

        public TupleType(params TypeIsa[] args) : this(new List<TypeIsa>(args))
        {
        }

        public IList<TypeIsa> Args { get; }

        public override T Dispatch<T>(TypeIsaVisitor<T> visitor)
        {
            return visitor.VisitTupleType(this);
        }
    }

    public class SumType : TypeIsa
    {
        public SumType(IList<TypeIsa> args)
        {
            Args = args;
        }

        public SumType(params TypeIsa[] args) : this(new List<TypeIsa>(args))
        {
        }

        public IList<TypeIsa> Args { get; }

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
        Real,
        String
    }

    public class PrimitiveType : TypeIsa
    {
        public PrimitiveType(SimpleType simpleType)
        {
            SimpleType = simpleType;
        }

        public SimpleType SimpleType { get; }

        public static PrimitiveType CreateBoolType()
        {
            return new PrimitiveType(SimpleType.Bool);
        }

        public static PrimitiveType CreateNatType()
        {
            return new PrimitiveType(SimpleType.Nat);
        }

        public static PrimitiveType CreateIntType()
        {
            return new PrimitiveType(SimpleType.Int);
        }
        
        public static PrimitiveType CreateRealType()
        {
            return new PrimitiveType(SimpleType.Real);
        }

        public static PrimitiveType CreateStringType()
        {
            return new PrimitiveType(SimpleType.String);
        }

        public override T Dispatch<T>(TypeIsaVisitor<T> visitor)
        {
            return visitor.VisitPrimitiveType(this);
        }
    }

    #endregion
}