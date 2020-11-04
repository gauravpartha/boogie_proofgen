using System.Collections.Generic;

namespace ProofGeneration.Isa
{

    public abstract class OuterDeclVisitor<R>
    {
        public R Visit(OuterDecl d)
        {
            return d.Dispatch(this);
        }

        public abstract R VisitFunDecl(FunDecl d);
          
        public abstract R VisitDefDecl(DefDecl d);

        public abstract R VisitLemmaDecl(LemmaDecl d);

        public abstract R VisitLemmasDecl(LemmasDecl d);

        public abstract R VisitLocaleDecl(LocaleDecl d);

        public abstract R VisitMLDecl(MLDecl d);
    }

    public abstract class TermVisitor<R>
    {
        public R Visit(Term t)
        {
            return t.Dispatch(this);
        }

        public IList<R> VisitList(IList<Term> list)
        {
            var result = new List<R>();
            foreach (var t in list)
            {
                result.Add(Visit(t));
            }
            return result;
        }

        public abstract R VisitTermApp(TermApp t);

        public abstract R VisitTermWithExplicitType(TermWithExplicitType t);

        public abstract R VisitTermList(TermList t);

        public abstract R VisitTermSet(TermSet t);

        public abstract R VisitTermRecord(TermRecord t);

        public abstract R VisitTermTuple(TermTuple t);

        public abstract R VisitTermIdent(TermIdent t);

        public abstract R VisitTermQuantifier(TermQuantifier t);

        public abstract R VisitTermCaseOf(TermCaseOf t);

        public abstract R VisitTermBinary(TermBinary t);

        public abstract R VisitTermUnary(TermUnary t);

        public abstract R VisitBoolConst(BoolConst t);

        public abstract R VisitNatConst(NatConst t);

        public abstract R VisitIntConst(IntConst t);

        public abstract R VisitStringConst(StringConst t);
    }

    public abstract class TypeIsaVisitor<R>
    {
        public R Visit(TypeIsa t)
        {
            return t.Dispatch(this);
        }

        public IList<R> VisitList(IList<TypeIsa> list)
        {
            var result = new List<R>();
            foreach(var t in list) {
                result.Add(Visit(t));
            }
            return result;
        }

        public abstract R VisitVarType(VarType t);

        public abstract R VisitTupleType(TupleType t);

        public abstract R VisitArrowType(ArrowType t);

        public abstract R VisitDataType(DataType t);

        public abstract R VisitPrimitiveType(PrimitiveType t);
    }
        
 }
