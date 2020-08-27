using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;

namespace ProofGeneration.VCProofGen
{
    interface IVCVarTranslator
    {
        bool TranslateBoogieVar(Variable v, out VCExprVar result);
        bool TranslateVCVar(VCExprVar v, out Variable result);
    }
}
