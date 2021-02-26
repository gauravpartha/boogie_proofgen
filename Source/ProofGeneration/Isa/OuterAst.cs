using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace ProofGeneration.Isa
{
    public class Theory
    {
        public readonly IList<OuterDecl> decls;
        public readonly IList<string> importTheories;
        public readonly string theoryName;

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
        public readonly IList<Tuple<IList<Term>, Term>> equations;

        //if type is null, then it must be inferred
        public readonly TypeIsa type;

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
        // arguments and right hand side 
        public readonly Tuple<IList<Term>, Term> equation;

        // if type is null, then type is inferred
        public readonly TypeIsa type;

        public DefDecl(string name, TypeIsa type, Tuple<IList<Term>, Term> equation) : base(name)
        {
            this.type = type;
            this.equation = equation;
        }


        public DefDecl(string name, Tuple<IList<Term>, Term> equation) : this(name, null, equation)
        {
        }

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
        // arguments and right hand side 
        public readonly Tuple<IList<Term>, Term> equation;

        // if type is null, then type is inferred
        public readonly TypeIsa type;

        public AbbreviationDecl(string name, TypeIsa type, Tuple<IList<Term>, Term> equation) : base(name)
        {
            this.type = type;
            this.equation = equation;
        }


        public AbbreviationDecl(string name, Tuple<IList<Term>, Term> equation) : this(name, null, equation)
        {
        }

        public override R Dispatch<R>(OuterDeclVisitor<R> visitor)
        {
            return visitor.VisitAbbreviationDecl(this);
        }
    }


    public class ContextElem
    {
        public readonly IList<string> assmLabels; //empty list is interpreted as having no assumption labels
        public readonly IList<Term> assumptions;
        public readonly IList<Tuple<TermIdent, TypeIsa>> fixedVariables;

        public ContextElem(IList<Tuple<TermIdent, TypeIsa>> fixedVariables, IList<Term> assumptions,
            IList<string> assmLabels)
        {
            Contract.Requires(assmLabels.Count == 0 || assumptions.Count == assmLabels.Count);
            this.fixedVariables = fixedVariables;
            this.assumptions = assumptions;
            this.assmLabels = assmLabels;
        }

        public bool IsEmpty()
        {
            return !fixedVariables.Any() && !assumptions.Any();
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
        public readonly ContextElem contextElem;
        public readonly Proof proof;
        public readonly Term statement;

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

    public class DeclareDecl : OuterDecl
    {
        public readonly string declaration;

        public DeclareDecl(string declaration) : base("Declare")
        {
            this.declaration = declaration;
        }

        public override R Dispatch<R>(OuterDeclVisitor<R> visitor)
        {
            return visitor.VisitDeclareDecl(this);
        }
    }


    public class MLDecl : OuterDecl
    {
        public enum MLKind
        {
            NORMAL,
            PROOF,
            VAL
        }

        public readonly string code;
        public readonly MLKind kind;

        public MLDecl(string code, MLKind kind = MLKind.NORMAL) : base("ML")
        {
            this.code = code;
            this.kind = kind;
        }

        public override R Dispatch<R>(OuterDeclVisitor<R> visitor)
        {
            return visitor.VisitMLDecl(this);
        }

        public string GetDeclId()
        {
            switch (kind)
            {
                case MLKind.NORMAL:
                    return "ML";
                case MLKind.PROOF:
                    return "ML_prf";
                case MLKind.VAL:
                    return "ML_val";
                default:
                    throw new ProofGenUnexpectedStateException(typeof(MLDecl), "no type");
            }
        }
    }
}