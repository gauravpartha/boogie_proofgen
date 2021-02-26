using ProofGeneration.Isa;

namespace ProofGeneration.BoogieIsaInterface
{
    public class BoogieContextIsa
    {
        public readonly Term absValTyMap;
        public readonly Term funContext;
        public readonly Term methodContext;
        public readonly Term rtypeEnv;
        public readonly Term varContext;

        public BoogieContextIsa(Term absValTyMap, Term methodContext, Term varContext, Term funContext, Term rtypeEnv)
        {
            this.absValTyMap = absValTyMap;
            this.methodContext = methodContext;
            this.varContext = varContext;
            this.funContext = funContext;
            this.rtypeEnv = rtypeEnv;
        }

        public static BoogieContextIsa CreateWithNewVarContext(BoogieContextIsa boogieContext, Term varContext)
        {
            return new BoogieContextIsa(boogieContext.absValTyMap, boogieContext.methodContext, varContext,
                boogieContext.funContext, boogieContext.rtypeEnv);
        }
    }
}