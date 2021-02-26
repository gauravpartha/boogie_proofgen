using ProofGeneration.Isa;

namespace ProofGeneration.Passification
{
    public class PassificationWitness
    {
        public PassificationWitness(
            Term varContext,
            Term modifiedVars,
            Term modifiedVarsRelation,
            Term stateRelation,
            Term oldStateRelation,
            Term passiveStates,
            Term constrainedVariables)
        {
            VarContext = varContext;
            ModifiedVars = modifiedVars;
            ModifiedVarsRelation = modifiedVarsRelation;
            StateRelation = stateRelation;
            OldStateRelation = oldStateRelation;
            PassiveStates = passiveStates;
            ConstrainedVariables = constrainedVariables;
            VarContext = varContext;
        }

        public Term VarContext { get; }
        public Term ModifiedVars { get; }
        public Term ModifiedVarsRelation { get; }
        public Term StateRelation { get; }
        public Term OldStateRelation { get; }
        public Term PassiveStates { get; }
        public Term ConstrainedVariables { get; }
    }
}