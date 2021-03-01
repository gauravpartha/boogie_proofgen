using System;
using System.Collections.Generic;
using ProofGeneration.Isa;

namespace ProofGeneration.BoogieIsaInterface.VariableTranslation
{
    internal class DeBruijnTranslation<T> : IVariableTranslation<T>
    {
        private readonly LinkedList<T> boundVariables = new LinkedList<T>();

        private readonly bool shiftFixedVar;

        private readonly Func<int, bool, Term> variableConstructor;
        private readonly IFixedVariableTranslation<T> variableTranslation;


        /// <param name="variableTranslation">Translation of non-bound variables in the context.</param>
        /// <param name="variableConstructor">
        ///     Function that constructs a Variable term given the integer id and whether it is bound
        ///     or not.
        /// </param>
        /// <param name="shiftFixedVar">Indicate whether non-bound variables should be shifted.</param>
        public DeBruijnTranslation(IFixedVariableTranslation<T> variableTranslation,
            Func<int, bool, Term> variableConstructor, bool shiftFixedVar)
        {
            this.variableTranslation = variableTranslation;
            this.variableConstructor = variableConstructor;
            this.shiftFixedVar = shiftFixedVar;
        }

        public void AddBoundVariable(T boundVar)
        {
            boundVariables.AddLast(boundVar);
        }

        public void DropLastBoundVariable()
        {
            boundVariables.RemoveLast();
        }

        public int NumBoundVariables()
        {
            return boundVariables.Count;
        }

        public Term TranslateVariable(T variable, out bool isBoundVar)
        {
            var idResult = TranslateVariableIdx(variable, out isBoundVar);
            return variableConstructor(idResult, isBoundVar);
        }

        public bool TryTranslateVariableId(T variable, out Term id, out bool isBoundVar)
        {
            id = new NatConst(TranslateVariableIdx(variable, out isBoundVar));
            return true;
        }

        private int TranslateVariableIdx(T variable, out bool isBoundVar)
        {
            var i = 0;
            isBoundVar = false;
            for (var curNode = boundVariables.Last; curNode != null; curNode = curNode.Previous)
            {
                if (curNode.Value.Equals(variable))
                {
                    isBoundVar = true;
                    break;
                }

                i++;
            }

            if (isBoundVar) return i;

            //variable is not bound
            return shiftFixedVar
                ? i + variableTranslation.VariableId(variable)
                : variableTranslation.VariableId(variable);
        }
    }
}