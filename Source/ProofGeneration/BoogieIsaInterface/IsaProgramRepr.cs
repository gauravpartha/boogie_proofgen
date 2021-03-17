namespace ProofGeneration.BoogieIsaInterface
{
    public class IsaGlobalProgramRepr
    {
        public readonly string axiomsDeclDef;
        public readonly string constantsDeclDef;
        public readonly string funcsDeclDef;
        public readonly string globalsDeclDef;

        public IsaGlobalProgramRepr(
            string funcsDeclDef,
            string axiomsDeclDef,
            string globalsDeclDef,
            string constantsDeclDef)
        {
            this.funcsDeclDef = funcsDeclDef;
            this.axiomsDeclDef = axiomsDeclDef;
            this.globalsDeclDef = globalsDeclDef;
            this.constantsDeclDef = constantsDeclDef;
        }
    }

    public class IsaProgramRepr
    {
        public IsaGlobalProgramRepr GlobalProgramRepr { get; }
        public readonly string cfgDeclDef;
        public readonly string localVarsDeclDef;
        public readonly string paramsDeclDef;
        public readonly string postconditionsDeclDef;
        public readonly string preconditionsDeclDef;

        public IsaProgramRepr(
            IsaGlobalProgramRepr globalProgramRepr,
            string preconditionsDeclDef,
            string postconditionsDeclDef,
            string paramsDeclDef,
            string localVarsDeclDef,
            string cfgDeclDef)
        {
            GlobalProgramRepr = globalProgramRepr;
            this.cfgDeclDef = cfgDeclDef;
            this.paramsDeclDef = paramsDeclDef;
            this.localVarsDeclDef = localVarsDeclDef;
            this.preconditionsDeclDef = preconditionsDeclDef;
            this.postconditionsDeclDef = postconditionsDeclDef;
        }
    }
}