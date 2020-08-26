using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;

namespace ProofGeneration.BoogieIsaInterface.VariableTranslation
{
    class DeBruijnFixedVarTranslation : IFixedVariableTranslation<Variable>
    {
        private readonly IDictionary<Variable, int> paramsAndLocalMapping;
        private readonly IDictionary<Variable, int> globalsMapping;

        public DeBruijnFixedVarTranslation(BoogieMethodData methodData)
        {
            paramsAndLocalMapping = new Dictionary<Variable, int>();
            globalsMapping = new Dictionary<Variable, int>();

            int id = 0;

            void AddVarsToMapping(IEnumerable<Variable> vars, IDictionary<Variable, int> dict)
            {
                foreach (Variable v in vars)
                {
                    if(dict.ContainsKey(v))
                    {
                        throw new ProofGenUnexpectedStateException(GetType(), "duplicate variables");
                    }
                    dict.Add(v, id);
                    id++;
                }
            }

            //order important
            AddVarsToMapping(methodData.InParams, paramsAndLocalMapping);
            AddVarsToMapping(methodData.Locals, paramsAndLocalMapping);
            AddVarsToMapping(methodData.GlobalVars.Union(methodData.Constants), globalsMapping);
        }

        public int VariableId(Variable variable)
        {
            if (paramsAndLocalMapping.TryGetValue(variable, out int localResult))
            {
                return localResult;
            } else if(globalsMapping.TryGetValue(variable, out int globalResult))
            {
                return globalResult;
            } else
            {
                throw new ProofGenUnexpectedStateException(GetType(), "cannot find variable " + variable);
            }
        }

    }
}
