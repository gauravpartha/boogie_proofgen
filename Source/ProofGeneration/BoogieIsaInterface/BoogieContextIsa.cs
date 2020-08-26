using ProofGeneration.Isa;

namespace ProofGeneration.BoogieIsaInterface
{
    public class BoogieContextIsa
    {
        public readonly Term absValTyMap;
        public readonly Term varContext;
        public readonly Term funContext;
        public readonly Term rtypeEnv;

        public BoogieContextIsa(Term absValTyMap, Term varContext, Term funContext, Term rtypeEnv)
        {
            this.absValTyMap = absValTyMap;
            this.varContext = varContext;
            this.funContext = funContext;
            this.rtypeEnv = rtypeEnv;
        }
    }
}
