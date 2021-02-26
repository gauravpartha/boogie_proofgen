using System;
using System.Collections.Generic;
using Microsoft.Boogie;

namespace ProofGeneration.BoogieIsaInterface.VariableTranslation
{
    public class SimpleFixedVarTranslation : IFixedVariableTranslation<Variable>
    {
        private readonly IDictionary<Variable, int> mapping;

        public SimpleFixedVarTranslation(IDictionary<Variable, int> mapping)
        {
            this.mapping = mapping;
        }

        public int VariableId(Variable varName)
        {
            return mapping[varName];
        }

        public string OutputMapping()
        {
            return string.Join(Environment.NewLine, mapping);
        }
    }
}