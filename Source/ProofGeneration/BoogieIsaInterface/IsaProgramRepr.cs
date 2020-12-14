﻿namespace ProofGeneration.BoogieIsaInterface
{
    public class IsaProgramRepr
    {
        public readonly string funcsDeclDef;
        public readonly string axiomsDeclDef;
        public readonly string cfgDeclDef;
        public readonly string globalsDeclDef;
        public readonly string constantsDeclDef;
        public readonly string paramsDeclDef;
        public readonly string localVarsDeclDef;

        public IsaProgramRepr(string funcsDeclDef, 
            string axiomsDeclDef, 
            string globalsDeclDef, 
            string constantsDeclDef, 
            string paramsDeclDef, 
            string localVarsDeclDef, 
            string cfgDeclDef)
        {
            this.funcsDeclDef = funcsDeclDef;
            this.axiomsDeclDef = axiomsDeclDef;
            this.globalsDeclDef = globalsDeclDef;
            this.constantsDeclDef = constantsDeclDef;
            this.cfgDeclDef = cfgDeclDef;
            this.paramsDeclDef = paramsDeclDef;
            this.localVarsDeclDef = localVarsDeclDef;
        }
    }
}
