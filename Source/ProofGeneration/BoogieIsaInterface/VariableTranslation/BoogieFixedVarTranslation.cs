using Microsoft.Boogie;

namespace ProofGeneration.BoogieIsaInterface.VariableTranslation
{
    class BoogieFixedVarTranslation
    {
        public IFixedVariableTranslation<Variable> VariableTranslation { get; }
        public IFixedVariableTranslation<TypeVariable> TyVariableTranslation { get; }

        public BoogieFixedVarTranslation(
            IFixedVariableTranslation<Variable> variableTranslation,
            IFixedVariableTranslation<TypeVariable> tyVariableTranslation)
        {
            this.VariableTranslation = variableTranslation;
            this.TyVariableTranslation = tyVariableTranslation;
        }
    }
}
