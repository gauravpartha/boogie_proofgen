using Microsoft.Boogie;

namespace ProofGeneration.BoogieIsaInterface.VariableTranslation
{
    public class BoogieVariableTranslation
    {
        public BoogieVariableTranslation(
            IVariableTranslation<Variable> variableTranslation,
            IVariableTranslation<TypeVariable> typeVarTranslation)
        {
            VarTranslation = variableTranslation;
            TypeVarTranslation = typeVarTranslation;
        }

        public IVariableTranslation<TypeVariable> TypeVarTranslation { get; }
        public IVariableTranslation<Variable> VarTranslation { get; }
    }
}