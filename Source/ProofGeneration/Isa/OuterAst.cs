using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace ProofGeneration.Isa
{

    public class Theory
    {
        public readonly string theoryName;
        public readonly IList<string> importTheories;
        public readonly IList<OuterDecl> decls;

        public Theory(string theoryName, IList<string> importTheories, IList<OuterDecl> decls)
        {
            this.theoryName = theoryName;
            this.importTheories = importTheories;
            this.decls = decls;
        }
    }

    public abstract class OuterDecl
    {
        public readonly string name;

        public OuterDecl(string name)
        {
            this.name = name;
        }

        public abstract R Dispatch<R>(OuterDeclVisitor<R> visitor);
    }

    public class FunDecl : OuterDecl
    {
        public readonly TypeIsa type;
        public readonly IList<Tuple<IList<Term>, Term>> equations;

        public FunDecl(string name, TypeIsa type, IList<Tuple<IList<Term>, Term>> equations) : base(name)
        {
            this.type = type;
            this.equations = equations;
        }

        public override R Dispatch<R>(OuterDeclVisitor<R> visitor)
        {
            return visitor.VisitFunDecl(this);
        }
    }

    public class DefDecl : OuterDecl
    {
        /* arguments and right hand side */
        public readonly Tuple<IList<Term>, Term> equation;

        public DefDecl(string name, Tuple<IList<Term>, Term> equation) : base(name)
        {
            this.equation = equation;
        }

        public override R Dispatch<R>(OuterDeclVisitor<R> visitor)
        {
            return visitor.VisitDefDecl(this);
        }
    }

    public class ContextElem
    {
        public readonly IList<Tuple<TermIdent, TypeIsa>> fixedVariables;
        public readonly IList<Term> assumptions;
        public readonly IList<string> assmLabels; //empty list is interpreted as having no assumption labels

        public ContextElem(IList<Tuple<TermIdent, TypeIsa>> fixedVariables, IList<Term> assumptions, IList<string> assmLabels)
        {
            Contract.Requires(assmLabels.Count == 0 || assumptions.Count == assmLabels.Count);
            this.fixedVariables = fixedVariables;
            this.assumptions = assumptions;
            this.assmLabels = assmLabels;
        }

        public static ContextElem CreateEmptyContext()
        {
            return new ContextElem(new List<Tuple<TermIdent, TypeIsa>>(), new List<Term>(), new List<string>());
        }

        public static ContextElem CreateWithFixedVars(IList<Tuple<TermIdent, TypeIsa>> fixedVariables)
        {
            return new ContextElem(fixedVariables, new List<Term>(), new List<string>());
        }

        public static ContextElem CreateWithAssumptions(IList<Term> assumptions)
        {
            return new ContextElem(new List<Tuple<TermIdent, TypeIsa>>(), assumptions, new List<string>());
        }
    }

    public class LocaleDecl : OuterDecl
    {
        public readonly ContextElem contextElem;

        public readonly IList<OuterDecl> body;

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
        public readonly ContextElem contextElem;
        public readonly Term statement;
        public readonly Proof proof;

        public LemmaDecl(string name, ContextElem contextElem, Term statement, Proof proof) : base(name)
        {
            this.contextElem = contextElem;
            this.statement = statement;
            this.proof = proof;
        }

        public LemmaDecl(string name, Term statement, Proof proof) :
            this(name, ContextElem.CreateEmptyContext(), statement, proof)
        {

        }

        public override R Dispatch<R>(OuterDeclVisitor<R> visitor)
        {
            return visitor.VisitLemmaDecl(this);
        }
    }

    public class LemmasDecl : OuterDecl
    {
        public readonly IList<string> thmNames;

        public LemmasDecl(string name, IList<string> thmNames) : base(name)
        {
            this.thmNames = thmNames;
        }

        public override R Dispatch<R>(OuterDeclVisitor<R> visitor)
        {
            return visitor.VisitLemmasDecl(this);
        }
    }
}
