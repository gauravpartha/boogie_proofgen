using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;

namespace ProofGeneration.VCProofGen
{
    public interface IVCVarFunTranslator
    {
        bool TranslateBoogieVar(Variable boogieVar, out VCExprVar result);
        bool TranslateVCVar(VCExprVar vcVar, out Variable result);
        bool TranslateBoogieFunction(Function boogieFun, out Function result);
        bool TranslateVCFunction(Function vcFun, out Function result);
    }
}