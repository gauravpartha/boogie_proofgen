using System.Collections.Generic;
using Microsoft.Boogie;

namespace ProofGeneration.BoogieIsaInterface.VariableTranslation
{
    class DeBruijnFixedTVarTranslation : IFixedVariableTranslation<TypeVariable>
    {
        private readonly IDictionary<TypeVariable, int> methodTyVarMapping;

        public DeBruijnFixedTVarTranslation(BoogieMethodData methodData)
        {
            methodTyVarMapping = new Dictionary<TypeVariable, int>();

            int id = 0;

            void AddVarsToMapping(IEnumerable<TypeVariable> vars, IDictionary<TypeVariable, int> dict)
            {
                foreach (var v in vars)
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
            AddVarsToMapping(methodData.TypeParams, methodTyVarMapping);
        }

        public int VariableId(TypeVariable tyVariable)
        {
            if(methodTyVarMapping.TryGetValue(tyVariable, out int localResult))
            {
                return localResult;
            } else
            {
                throw new ProofGenUnexpectedStateException(GetType(), "cannot find variable " + tyVariable);
            }
        }
    }
}
