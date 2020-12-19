using System;
using Microsoft.Boogie;
using ProofGeneration.Isa;

namespace ProofGeneration.BoogieIsaInterface.VariableTranslation
{
    
    /// <summary>
    /// fixed value variables are assumed not to be in the same domain as de-bruijn variables (so they need not be shifted)
    /// fixed type variables are shifted
    /// </summary>
    class DeBruijnVarFactory : IVariableTranslationFactory
    {
        private readonly IFixedVariableTranslation<Variable> varTranslation;
        private readonly DeBruijnFixedTVarTranslation tvarTranslation;
        private readonly BoogieGlobalData globalData;

        private readonly Func<int, bool, Term> valueVarConstructor = IsaBoogieTerm.VariableConstr;
        private readonly Func<int, bool, Term> typeVarConstructor = (i,isBound) => IsaBoogieType.TVar(i);

        public DeBruijnVarFactory(
            IFixedVariableTranslation<Variable> varTranslation,
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
                    new DeBruijnTranslation<Variable>(varTranslation, valueVarConstructor, false),
                    new DeBruijnTranslation<TypeVariable>(tvarTranslation, typeVarConstructor, true)
                    );
        }

        public BoogieVariableTranslation CreateEmptyTranslation()
        {
            return new BoogieVariableTranslation(
                    new DeBruijnTranslation<Variable>(varTranslation, valueVarConstructor, false),
                    new DeBruijnTranslation<TypeVariable>(new DeBruijnFixedTVarTranslation(BoogieMethodData.CreateEmpty()), typeVarConstructor, true)
                    );
        }
    }
}
