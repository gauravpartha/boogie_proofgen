using System.Collections.Generic;
using Microsoft.Boogie;
using ProofGeneration.Isa;

namespace ProofGeneration.BoogieIsaInterface.VariableTranslation
{
    //TODO support bound variables, might make sense to extract part of DeBruijnTranslation that does this and to re-use the code
    public class SimpleVarSubstitution<T> : IVariableTranslation<T>
    {
        private readonly IDictionary<T, Term> substitution;
        public SimpleVarSubstitution(IDictionary<T, Term> substitution)
        {
            this.substitution = substitution;
        }

        public void AddBoundVariable(T boundVar)
        {
            //TODO
            throw new System.NotImplementedException();
        }

        public void DropLastBoundVariable()
        {
            //TODO
            throw new System.NotImplementedException();
        }

        public int NumBoundVariables()
        {
            //TODO
            throw new System.NotImplementedException();
        }

        public Term TranslateVariable(T variable)
        {
            return substitution[variable];
        }

        public bool TryTranslateVariableId(T variable, out Term id)
        {
            throw new System.NotSupportedException();
        }
    }
}