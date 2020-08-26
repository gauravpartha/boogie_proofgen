using Microsoft.Boogie;
namespace ProofGeneration.BoogieIsaInterface.VariableTranslation
{
    public class BoogieVariableTranslation
    {
        public IVariableTranslation<TypeVariable> TypeVarTranslation { get; }
        public IVariableTranslation<Variable> VarTranslation { get; }

        public BoogieVariableTranslation(
            IVariableTranslation<Variable> variableTranslation,
            IVariableTranslation<TypeVariable> typeVarTranslation)
        {
            this.VarTranslation = variableTranslation;
            this.TypeVarTranslation = typeVarTranslation;
        }
    }
}
