using Isabelle.Ast;

namespace ProofGeneration.BoogieIsaInterface.VariableTranslation
{
    public interface IVariableTranslation<T>
    {
        void AddBoundVariable(T boundVar);

        void DropLastBoundVariable();

        int NumBoundVariables();

        /// <summary>
        ///     Translates <paramref name="variable" /> to an expression. This can but need not be the corresponding variable
        ///     at the term level.
        /// </summary>
        /// <param name="variable"></param>
        /// <param name="isBoundVar"></param>
        /// <returns></returns>
        Term TranslateVariable(T variable, out bool isBoundVar);

        /// <summary>
        ///     Translates <paramref name="variable" /> to the corresponding term representing its identifier.
        ///     For example, variable "x" may be represented by an integer i (its id), while the variable at the term level
        ///     would be (Var i), where "Var" is the variable constructor.
        ///     Since variables may be translated to expressions, the implementation may not know what the id is.
        /// </summary>
        /// <param name="variable"></param>
        /// <param name="id"></param>
        /// <param name="isBoundVar"></param>
        /// <returns></returns>
        bool TryTranslateVariableId(T variable, out Term id, out bool isBoundVar);
        
        /// <summary>
        /// Same as <see cref="TryTranslateVariableId(T,out Isabelle.Ast.Term,out bool)"/>, but only returns true if the
        /// identifier is represented by a number and if so, returns the corresponding integer (instead of the term)
        /// </summary>
        bool TryTranslateVariableIntId(T variable, out int id, out bool isBoundVar);
    }
}