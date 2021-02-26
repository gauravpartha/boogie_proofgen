using Microsoft.Boogie;

namespace ProofGeneration.BoogieIsaInterface.VariableTranslation
{
    internal class BoogieFixedVarTranslation
    {
        public BoogieFixedVarTranslation(
            IFixedVariableTranslation<Variable> variableTranslation,
            IFixedVariableTranslation<TypeVariable> tyVariableTranslation)
        {
            VariableTranslation = variableTranslation;
            TyVariableTranslation = tyVariableTranslation;
        }

        public IFixedVariableTranslation<Variable> VariableTranslation { get; }
        public IFixedVariableTranslation<TypeVariable> TyVariableTranslation { get; }
    }
}