namespace ProofGeneration.BoogieIsaInterface.VariableTranslation
{
    public interface IVariableTranslation<T>
    {
        void AddBoundVariable(T boundVar);

        void DropLastBoundVariable();

        int NumBoundVariables();

        int TranslateVariable(T variable);
    }
}
