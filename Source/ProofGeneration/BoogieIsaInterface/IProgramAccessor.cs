using Microsoft.Boogie;
using ProofGeneration.Isa;

namespace ProofGeneration.BoogieIsaInterface
{
    public interface IProgramAccessor
    {
        public string TheoryName();
        
        public Term FunctionsDecl();
        public Term AxiomsDecl();
        public Term PreconditionsDecl();
        public string PreconditionsDeclName();
        public Term PostconditionsDecl();
        public string PostconditionsDeclName();
        
        public Term CfgDecl();

        //params + local variables
        public Term ParamsAndLocalsDecl();

        //globals + constant variables
        public Term ConstsAndGlobalsDecl();

        public string ConstsDecl();
        public string GlobalsDecl();
        public string ParamsDecl();
        public string LocalsDecl();

        public Term VarContext();

        public string MembershipLemma(Declaration d);

        public IsaBlockInfo BlockInfo();

        public string GlobalsLocalsDisjointLemma();
        public string GlobalsAtMostMax();
        public string LocalsAtLeastMin();

        public string LookupVarTyLemma(Variable v);
    }
}