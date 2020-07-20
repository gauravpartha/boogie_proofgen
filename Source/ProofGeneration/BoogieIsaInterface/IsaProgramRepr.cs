using ProofGeneration.Isa;

namespace ProofGeneration.BoogieIsaInterface
{
    class IsaProgramRepr
    {
        public readonly TermIdent funcsDeclDef;
        public readonly TermIdent axiomsDeclDef;
        public readonly TermIdent cfgDeclDef;
        public readonly TermIdent paramsDeclDef;
        public readonly TermIdent localVarsDeclDef;

        public IsaProgramRepr(TermIdent funcsDeclDef, TermIdent axiomsDeclDef, TermIdent paramsDeclDef,  TermIdent localVarsDeclDef, TermIdent cfgDeclDef)
        {
            this.funcsDeclDef = funcsDeclDef;
            this.axiomsDeclDef = axiomsDeclDef;
            this.cfgDeclDef = cfgDeclDef;
            this.paramsDeclDef = paramsDeclDef;
            this.localVarsDeclDef = localVarsDeclDef;
        }
    }
}
