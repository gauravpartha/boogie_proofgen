using System;
using System.Collections.Generic;
using ProofGeneration.Isa;

namespace ProofGeneration.BoogieIsaInterface.VariableTranslation
{
    class DeBruijnTranslation<T> : IVariableTranslation<T>
    {
        private readonly IFixedVariableTranslation<T> variableTranslation;

        private readonly LinkedList<T> boundVariables = new LinkedList<T>();

        private readonly Func<int, Term> variableConstructor;


        public DeBruijnTranslation(IFixedVariableTranslation<T> variableTranslation, Func<int, Term> variableConstructor)
        {
            this.variableTranslation = variableTranslation;
            this.variableConstructor = variableConstructor;
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
        
        private int TranslateVariableIdx(T variable)
        {
            int i = 0;
            bool isBoundVar = false;
            for (var curNode = boundVariables.Last; curNode != null; curNode = curNode.Previous)
            {
                if (curNode.Value.Equals(variable))
                {
                    isBoundVar = true;
                    break;
                }
                i++;
            }

            if (isBoundVar)
            {
                return i;
            }
            else
            {
                //variable is not bound, need to shift id by number of quantifiers
                return variableTranslation.VariableId(variable) + i;
            }
        }

        public Term TranslateVariable(T variable)
        {
            return variableConstructor(TranslateVariableIdx(variable));
        }

        public bool TryTranslateVariableId(T variable, out Term id)
        {
            id = new IntConst(TranslateVariableIdx(variable));
            return true;
        }
    }
}
