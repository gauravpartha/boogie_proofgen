using System.Collections.Generic;

namespace ProofGeneration.Isa
{
    class IsaCommonTerms
    {

        private static readonly TermIdent SomeId = TermIdentFromName("Some");
        private static readonly TermIdent NoneId = TermIdentFromName("None");
        private static readonly TermIdent TheId = TermIdentFromName("the");
        public static TermIdent FstId { get;  } = TermIdentFromName("fst");
        private static readonly TermIdent SndId = TermIdentFromName("snd");
        private static readonly TermIdent InlId = TermIdentFromName("Inl");
        private static readonly TermIdent InrId = TermIdentFromName("Inr");
        private static readonly TermIdent AppendId = TermIdentFromName("append");
        private static readonly TermIdent MapId = TermIdentFromName("map");
        private static readonly TermIdent SetOfListId = TermIdentFromName("set");
        private static readonly TermIdent ListAllId = TermIdentFromName("list_all");
        private static readonly TermIdent MemberId = TermIdentFromName("Set.member");
        private static readonly TermIdent SetMaxId = TermIdentFromName("Max");
        private static readonly TermIdent SetMinId = TermIdentFromName("Min");
        private static readonly TermIdent SetUnionId = TermIdentFromName("Set.union");
        private static readonly TermIdent SetInterId = TermIdentFromName("Set.inter");
        private static readonly TermIdent Nth = TermIdentFromName("nth");

        public static TermIdent EmptyList => TermIdentFromName("[]");
        public static TermIdent EmptySet => TermIdentFromName("{}");

        public static Term EmptyMap => TermIdentFromName("Map.empty");
        
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

        public static Term Map(Term fun, Term list)
        {
            return new TermApp(MapId, fun, list);
        }
        
        public static Term SetOfList(Term list)
        {
            return new TermApp(SetOfListId, list);
        }

        /// <summary>
        /// Lookup element at index <paramref name="idx"/>
        /// </summary>
        public static Term ListLookup(Term list, int idx)
        {
            return new TermApp(Nth, new List<Term> { list, new NatConst(idx) });
        }

        public static Term ListAll(Term pred, Term list)
        {
            return new TermApp(ListAllId, pred, list);
        }

        public static Term Elem(Term element, Term set)
        {
            return new TermApp(MemberId, new List<Term> { element, set });
        }

        public static Term SetUnion(Term set1, Term set2)
        {
            return new TermApp(SetUnionId, new List<Term> { set1, set2 });
        }

        public static Term SetInter(Term set1, Term set2)
        {
            return new TermApp(SetInterId, new List<Term> { set1, set2 });
        }
        
        public static Term SetMax(Term set)
        {
            return new TermApp(SetMaxId, set);
        }
        
        public static Term SetMin(Term set)
        {
            return new TermApp(SetMinId, set);
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
