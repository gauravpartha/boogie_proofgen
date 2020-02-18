using System.Collections.Generic;

namespace ProofGeneration.Isa
{
    class IsaCommonTerms
    {

        private static readonly TermIdent SomeId = TermIdentFromName("Some");
        private static readonly TermIdent NoneId = TermIdentFromName("None");
        private static readonly TermIdent FstId = TermIdentFromName("fst");
        private static readonly TermIdent SndId = TermIdentFromName("snd");

        public static Term SomeOption(Term arg)
        {
            return new TermApp(SomeId, new List<Term>() { arg });
        }

        public static Term NoneOption()
        {
            return new TermApp(NoneId, new List<Term>());
        }

        public static Term Fst(Term arg)
        {
            return new TermApp(FstId, new List<Term>() { arg });
        }

        public static Term Snd(Term arg)
        {
            return new TermApp(SndId, new List<Term>() { arg });
        }

        public static TermIdent TermIdentFromName(string name)
        {
            return new TermIdent(new SimpleIdentifier(name));
        }       
    }
}
