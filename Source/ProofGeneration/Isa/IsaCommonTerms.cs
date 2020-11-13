using System.Collections.Generic;

namespace ProofGeneration.Isa
{
    class IsaCommonTerms
    {

        private static readonly TermIdent SomeId = TermIdentFromName("Some");
        private static readonly TermIdent NoneId = TermIdentFromName("None");
        private static readonly TermIdent TheId = TermIdentFromName("the");
        private static readonly TermIdent FstId = TermIdentFromName("fst");
        private static readonly TermIdent SndId = TermIdentFromName("snd");
        private static readonly TermIdent InlId = TermIdentFromName("Inl");
        private static readonly TermIdent InrId = TermIdentFromName("Inr");
        private static readonly TermIdent AppendId = TermIdentFromName("append");
        private static readonly TermIdent SetOfListId = TermIdentFromName("set");
        private static readonly TermIdent MemberId = TermIdentFromName("Set.member");

        public static TermIdent EmptyList => TermIdentFromName("[]");
        public static Term Let(Identifier boundVar, TypeIsa boundVarType, Term termSubst, Term body)
        {
            return new TermApp(
                new TermApp(new TermIdent(new SimpleIdentifier("Let")), termSubst),
                TermQuantifier.Lambda(new List<Identifier>(){boundVar}, 
                    new List<TypeIsa>() {boundVarType}, body) 
                );
        }
        
        public static Term Let(Identifier boundVar, Term termSubst, Term body)
        {
            return new TermApp(
                new TermApp(new TermIdent(new SimpleIdentifier("Let")), termSubst),
                TermQuantifier.Lambda(new List<Identifier>(){boundVar}, null, body) 
                );
        }
        
        public static Term SomeOption(Term arg)
        {
            return new TermApp(SomeId, new List<Term>() { arg });
        }

        public static Term NoneOption()
        {
            return new TermApp(NoneId, new List<Term>());
        }

        public static Term TheOption(Term arg)
        {
            return new TermApp(TheId, arg);
        }

        public static Term Fst(Term arg)
        {
            return new TermApp(FstId, arg);
        }

        public static Term Snd(Term arg)
        {
            return new TermApp(SndId, arg);
        }

        public static Term Inl(Term arg)
        {
            return new TermApp(InlId, arg);
        }

        public static Term Inr(Term arg)
        {
            return new TermApp(InrId, arg);
        } 

        public static Term Unit()
        {
            return TermIdentFromName("()");
        }

        public static Term AppendList(Term list1, Term list2)
        {
            return new TermApp(AppendId, new List<Term> { list1, list2 });
        }
        
        public static Term SetOfList(Term list)
        {
            return new TermApp(SetOfListId, list);
        }

        public static Term Elem(Term element, Term set)
        {
            return new TermApp(MemberId, new List<Term> { element, set });
        }

        public static TermIdent TermIdentFromName(string name)
        {
            return new TermIdent(new SimpleIdentifier(name));
        }

        public static TermIdent TermIdentFromDecl(OuterDecl decl)
        {
            return TermIdentFromName(decl.name);
        }
    }
}
