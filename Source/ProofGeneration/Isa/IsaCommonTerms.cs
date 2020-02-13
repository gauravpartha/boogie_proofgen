using System.Collections.Generic;

namespace ProofGeneration.Isa
{
    class IsaCommonTerms
    {
        public static Term SomeOption(Term arg)
        {
            return new TermApp(TermIdentFromName("Some"), new List<Term>() { arg });
        }

        public static Term NoneOption()
        {
            return new TermApp(TermIdentFromName("None"), new List<Term>());
        }

        public static TermIdent TermIdentFromName(string name)
        {
            return new TermIdent(new SimpleIdentifier(name));
        }
    }
}
