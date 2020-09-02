using System;
using Microsoft.Boogie;
using ProofGeneration.Isa;

namespace ProofGeneration.BoogieIsaInterface.VariableTranslation
{
    class DeBruijnVarFactory : IVariableTranslationFactory
    {
        private readonly DeBruijnFixedVarTranslation varTranslation;
        private readonly DeBruijnFixedTVarTranslation tvarTranslation;
        private readonly BoogieGlobalData globalData;

        private readonly Func<int, Term> valueVarConstructor = i => IsaBoogieTerm.Var(i);
        private readonly Func<int, Term> typeVarConstructor = i => IsaBoogieType.TVar(i);

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
                    new DeBruijnTranslation<Variable>(varTranslation, valueVarConstructor),
                    new DeBruijnTranslation<TypeVariable>(tvarTranslation, typeVarConstructor)
                    );
        }

        public BoogieVariableTranslation CreateEmptyTranslation()
        {
            return new BoogieVariableTranslation(
                    new DeBruijnTranslation<Variable>(new DeBruijnFixedVarTranslation(BoogieMethodData.CreateEmpty()), valueVarConstructor),
                    new DeBruijnTranslation<TypeVariable>(new DeBruijnFixedTVarTranslation(BoogieMethodData.CreateEmpty()), typeVarConstructor)
                    );
        }

        public BoogieVariableTranslation CreateOnlyGlobalTranslation()
        {
            return new BoogieVariableTranslation(
                    new DeBruijnTranslation<Variable>(new DeBruijnFixedVarTranslation(BoogieMethodData.CreateOnlyGlobal(globalData)), valueVarConstructor),
                    new DeBruijnTranslation<TypeVariable>(new DeBruijnFixedTVarTranslation(BoogieMethodData.CreateOnlyGlobal(globalData)), typeVarConstructor)
                    );
        }
    }
}
