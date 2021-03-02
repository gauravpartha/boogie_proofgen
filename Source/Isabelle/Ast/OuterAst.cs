using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Isabelle.Ast
{
    public class Theory
    {
        public Theory(string theoryName, IList<string> importTheories, IList<OuterDecl> decls)
        {
            TheoryName = theoryName;
            ImportTheories = importTheories;
            Decls = decls;
        }

        public IList<OuterDecl> Decls { get; }
        public IList<string> ImportTheories { get; }
        public string TheoryName { get; }
    }

    public abstract class OuterDecl
    {
        protected OuterDecl(string name)
        {
            Name = name;
        }

        public string Name { get; }

        public abstract R Dispatch<R>(OuterDeclVisitor<R> visitor);
    }

    public class FunDecl : OuterDecl
    {
        public FunDecl(string name, TypeIsa type, IList<Tuple<IList<Term>, Term>> equations) : base(name)
        {
            Type = type;
            Equations = equations;
        }

        public IList<Tuple<IList<Term>, Term>> Equations { get; }

        //if type is null, then it must be inferred
        public TypeIsa Type { get; }

        public override R Dispatch<R>(OuterDeclVisitor<R> visitor)
        {
            return visitor.VisitFunDecl(this);
        }
    }

    public class DefDecl : OuterDecl
    {
        public DefDecl(string name, TypeIsa type, Tuple<IList<Term>, Term> equation) : base(name)
        {
            Type = type;
            Equation = equation;
        }


        public DefDecl(string name, Tuple<IList<Term>, Term> equation) : this(name, null, equation)
        {
        }

        // arguments and right hand side 
        public Tuple<IList<Term>, Term> Equation { get; }

        // if type is null, then type is inferred
        public TypeIsa Type { get; }

        public static DefDecl CreateWithoutArg(string name, Term rhs)
        {
            return new DefDecl(name, new Tuple<IList<Term>, Term>(new List<Term>(), rhs));
        }

        public override R Dispatch<R>(OuterDeclVisitor<R> visitor)
        {
            return visitor.VisitDefDecl(this);
        }
    }

    public class AbbreviationDecl : OuterDecl
    {
        public AbbreviationDecl(string name, TypeIsa type, Tuple<IList<Term>, Term> equation) : base(name)
        {
            Type = type;
            Equation = equation;
        }


        public AbbreviationDecl(string name, Tuple<IList<Term>, Term> equation) : this(name, null, equation)
        {
        }

        // arguments and right hand side 
        public Tuple<IList<Term>, Term> Equation { get; }

        // if type is null, then type is inferred
        public TypeIsa Type { get; }

        public override R Dispatch<R>(OuterDeclVisitor<R> visitor)
        {
            return visitor.VisitAbbreviationDecl(this);
        }
    }


    public class ContextElem
    {
        public ContextElem(IList<Tuple<TermIdent, TypeIsa>> fixedVariables, IList<Term> assumptions,
            IList<string> assmLabels)
        {
            Contract.Requires(assmLabels.Count == 0 || assumptions.Count == assmLabels.Count);
            FixedVariables = fixedVariables;
            Assumptions = assumptions;
            AssmLabels = assmLabels;
        }

        public IList<string> AssmLabels { get; } //empty list is interpreted as having no assumption labels
        public IList<Term> Assumptions { get; }
        public IList<Tuple<TermIdent, TypeIsa>> FixedVariables { get; }

        public bool IsEmpty()
        {
            return !FixedVariables.Any() && !Assumptions.Any();
        }

        public static ContextElem CreateEmptyContext()
        {
            return new ContextElem(new List<Tuple<TermIdent, TypeIsa>>(), new List<Term>(), new List<string>());
        }

        public static ContextElem CreateWithFixedVars(IList<Tuple<TermIdent, TypeIsa>> fixedVariables)
        {
            return new ContextElem(fixedVariables, new List<Term>(), new List<string>());
        }

        public static ContextElem CreateWithAssumptions(Term assumption)
        {
            return new ContextElem(new List<Tuple<TermIdent, TypeIsa>>(), new List<Term> {assumption},
                new List<string>());
        }

        public static ContextElem CreateWithAssumptions(IList<Term> assumptions)
        {
            return new ContextElem(new List<Tuple<TermIdent, TypeIsa>>(), assumptions, new List<string>());
        }

        public static ContextElem CreateWithAssumptions(IList<Term> assumptions, IList<string> assmLabels)
        {
            return new ContextElem(new List<Tuple<TermIdent, TypeIsa>>(), assumptions, assmLabels);
        }
    }

    public class LocaleDecl : OuterDecl
    {
        public readonly IList<OuterDecl> body;
        public readonly ContextElem contextElem;

        public LocaleDecl(string name, ContextElem contextElem, IList<OuterDecl> body) : base(name)
        {
            this.contextElem = contextElem;
            this.body = body;
        }

        public override R Dispatch<R>(OuterDeclVisitor<R> visitor)
        {
            return visitor.VisitLocaleDecl(this);
        }
    }

    public class LemmaDecl : OuterDecl
    {
        public LemmaDecl(string name, ContextElem contextElem, Term statement, Proof proof) : base(name)
        {
            ContextElem = contextElem;
            Statement = statement;
            Proof = proof;
        }

        public LemmaDecl(string name, Term statement, Proof proof) :
            this(name, ContextElem.CreateEmptyContext(), statement, proof)
        {
        }

        public ContextElem ContextElem { get; }
        public Proof Proof { get; }
        public Term Statement { get; }

        public override R Dispatch<R>(OuterDeclVisitor<R> visitor)
        {
            return visitor.VisitLemmaDecl(this);
        }
    }

    public class LemmasDecl : OuterDecl
    {
        public LemmasDecl(string name, IList<string> thmNames) : base(name)
        {
            ThmNames = thmNames;
        }

        public IList<string> ThmNames { get; }

        public override R Dispatch<R>(OuterDeclVisitor<R> visitor)
        {
            return visitor.VisitLemmasDecl(this);
        }
    }

    public class DeclareDecl : OuterDecl
    {
        public DeclareDecl(string declaration) : base("Declare")
        {
            Declaration = declaration;
        }

        public string Declaration { get; }

        public override R Dispatch<R>(OuterDeclVisitor<R> visitor)
        {
            return visitor.VisitDeclareDecl(this);
        }
    }


    public class MLDecl : OuterDecl
    {
        public enum MLKind
        {
            Normal,
            Proof,
            Val
        }

        public MLDecl(string code, MLKind kind = MLKind.Normal) : base("ML")
        {
            Code = code;
            Kind = kind;
        }

        public string Code { get; }
        public MLKind Kind { get; }

        public override R Dispatch<R>(OuterDeclVisitor<R> visitor)
        {
            return visitor.VisitMLDecl(this);
        }

        public string GetDeclId()
        {
            switch (Kind)
            {
                case MLKind.Normal:
                    return "ML";
                case MLKind.Proof:
                    return "ML_prf";
                case MLKind.Val:
                    return "ML_val";
                default:
                    throw new IsabelleException("no type");
            }
        }
    }
}