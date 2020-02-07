using Microsoft.Basetypes;
using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace ProofGeneration
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
    }

    class Wildcard : Identifier { }

    #region Term
    public abstract class Term {

        public abstract T Dispatch<T>(TermVisitor<T> visitor);
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
        public readonly Term fun;
        public readonly IList<Term> arg; //technically don't require lists, but allows one to keep structure

        public TermApp(Term fun, IList<Term> arg)
        {
            this.fun = fun;
            this.arg = arg;
        }

        public override T Dispatch<T>(TermVisitor<T> visitor)
        {
            return visitor.VisitTermApp(this);
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

    public class TermNAry : Term
    {
        public readonly IList<Term> args;

        public readonly TermOpCode op;

        public enum TermOpCode
        {
            EQ,
            LE,
            AND, OR, IMPLIES, NOT,
            ADD
        }

        public TermNAry(IList<Term> args, TermOpCode op)
        {
            this.args = args;
            this.op = op;
            if(NumOfArgs(op) != args.Count())
            {
                throw new ProofGenUnexpectedStateException<TermNAry>(this.GetType(), 
                    "expected " + NumOfArgs(op) + " arguments, but only have " + args.Count);
            }
        }

        protected int NumOfArgs(TermOpCode op)
        {
            switch(op)
            {
                case TermOpCode.AND:
                case TermOpCode.IMPLIES:
                case TermOpCode.OR:
                case TermOpCode.ADD:
                    return 2;
                case TermOpCode.NOT:
                    return 1;
                default:
                    throw new NotImplementedException();
            }
        }

        public override T Dispatch<T>(TermVisitor<T> visitor)
        {
            return visitor.VisitTermNAry(this);
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
            Contract.Invariant(this.n >= 0);
        }
    }

    public class IntConst : Term
    {
        public readonly BigNum i;

        public IntConst(BigNum i)
        {
            this.i = i;
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
        public readonly string name;
        public readonly IList<TypeIsa> args;

        public DataType(string name, IList<TypeIsa> args)
        {
            this.name = name;
            this.args = args;
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

        public override T Dispatch<T>(TypeIsaVisitor<T> visitor)
        {
            return visitor.VisitTupleType(this);
        }
    }

    public enum SimpleType
    {
        Bool, Nat, Int, String
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
