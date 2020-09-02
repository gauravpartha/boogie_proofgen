using Microsoft.Boogie;
using System.Collections.Generic;

namespace ProofGeneration.ProgramToVCProof
{
    public static class TypeUtil
    {

        public static bool IsPrimitive(Type type)
        {
            return type is BasicType;
        }
        
        ///<summary>
        ///Splits <paramref name="typeVars"/> into the explicit (i.e., does not appear freely and hence cannot be inferred
        /// from a concrete instantiation) and implicit type variables w.r.t. <paramref name="inputTypes"/>
        ///</summary>
        public static void SplitTypeParams(
            IEnumerable<TypeVariable> typeVars, 
            IEnumerable<Type> inputTypes,
            out List<TypeVariable> explicitTypeVars,
            out List<TypeVariable> implicitTypeVars)
        {
            var appearingTVars = new HashSet<TypeVariable>();
            foreach (var ty in inputTypes)
            {
                appearingTVars.UnionWith(ty.FreeVariables);
            }

            explicitTypeVars = new List<TypeVariable>();
            implicitTypeVars = new List<TypeVariable>();
                    
            foreach (var typeVar in typeVars)
            {
                if (appearingTVars.Contains(typeVar))
                {
                    implicitTypeVars.Add(typeVar);
                }
                else
                {
                    explicitTypeVars.Add(typeVar);
                }
            }
        }
    }
}