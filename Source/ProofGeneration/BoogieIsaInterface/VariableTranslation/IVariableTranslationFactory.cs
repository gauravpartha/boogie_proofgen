namespace ProofGeneration.BoogieIsaInterface.VariableTranslation
{
    public interface IVariableTranslationFactory
    {
        BoogieVariableTranslation CreateTranslation();

        BoogieVariableTranslation CreateEmptyTranslation();
    }
}