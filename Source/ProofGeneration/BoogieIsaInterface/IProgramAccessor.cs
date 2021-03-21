using Isabelle.Ast;
using Microsoft.Boogie;

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

        //does not take global variables into account
        public string ConstantMembershipLemma(Variable c);

        public IsaBlockInfo BlockInfo();

        public string GlobalsLocalsDisjointLemma();
        public string GlobalsAtMostMax();
        public string LocalsAtLeastMin();
        public string FuncsWfTyLemma();
        public string VarContextWfTyLemma();
        public string LookupVarDeclLemma(Variable v);
        public string LookupVarTyLemma(Variable v);
    }
}