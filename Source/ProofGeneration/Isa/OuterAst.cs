using System;
using System.Collections.Generic;

namespace ProofGeneration
{
    public enum commonTheories
    {
        MAIN, LANG
    }

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

}
