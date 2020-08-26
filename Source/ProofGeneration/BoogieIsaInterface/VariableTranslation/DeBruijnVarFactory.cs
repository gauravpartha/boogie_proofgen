using Microsoft.Boogie;

namespace ProofGeneration.BoogieIsaInterface.VariableTranslation
{
    class DeBruijnVarFactory : IVariableTranslationFactory
    {
        private readonly DeBruijnFixedVarTranslation varTranslation;
        private readonly DeBruijnFixedTVarTranslation tvarTranslation;
        private readonly BoogieGlobalData globalData;

        public DeBruijnVarFactory(DeBruijnFixedVarTranslation varTranslation,
            DeBruijnFixedTVarTranslation tvarTranslation,
            BoogieGlobalData boogieGlobalData)
        {
            this.varTranslation = varTranslation;
            this.tvarTranslation = tvarTranslation;
            this.globalData = boogieGlobalData;
        }

        public BoogieVariableTranslation CreateTranslation()
        {
            return new BoogieVariableTranslation(
                    new DeBruijnTranslation<Variable>(varTranslation),
                    new DeBruijnTranslation<TypeVariable>(tvarTranslation)
                    );
        }

        public BoogieVariableTranslation CreateEmptyTranslation()
        {
            return new BoogieVariableTranslation(
                    new DeBruijnTranslation<Variable>(new DeBruijnFixedVarTranslation(BoogieMethodData.CreateEmpty())),
                    new DeBruijnTranslation<TypeVariable>(new DeBruijnFixedTVarTranslation(BoogieMethodData.CreateEmpty()))
                    );
        }

        public BoogieVariableTranslation CreateOnlyGlobalTranslation()
        {
            return new BoogieVariableTranslation(
                    new DeBruijnTranslation<Variable>(new DeBruijnFixedVarTranslation(BoogieMethodData.CreateOnlyGlobal(globalData))),
                    new DeBruijnTranslation<TypeVariable>(new DeBruijnFixedTVarTranslation(BoogieMethodData.CreateOnlyGlobal(globalData)))
                    );
        }
    }
}
