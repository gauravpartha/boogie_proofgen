using System.Collections.Generic;

namespace ProofGeneration.BoogieIsaInterface.VariableTranslation
{
    class DeBruijnTranslation<T> : IVariableTranslation<T>
    {
        private readonly IFixedVariableTranslation<T> variableTranslation;

        private LinkedList<T> boundVariables = new LinkedList<T>();


        public DeBruijnTranslation(IFixedVariableTranslation<T> variableTranslation)
        {
            this.variableTranslation = variableTranslation;
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

        public int TranslateVariable(T variable)
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

    }
}
