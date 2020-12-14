namespace ProofGeneration.BoogieIsaInterface.VariableTranslation
{
    public interface IFixedVariableTranslation<T>
    {
        int VariableId(T varName);

        public string OutputMapping();
    }
}
