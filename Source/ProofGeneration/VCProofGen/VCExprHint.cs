using ProofGeneration.Isa;
using ProofGeneration.IsaML;

namespace ProofGeneration.VCProofGen
{
    public class VCExprHint : INodeML
    {
        //if it is null, then no lemma should be applied, otherwise the lemma should be applied to rewrite the VC expression
        public LemmaDecl LemmaToApplyBefore { get; }

        public VCExprHint(LemmaDecl lemmaToApplyBefore)
        {
            LemmaToApplyBefore = lemmaToApplyBefore;
        }

        public static VCExprHint EmptyExprHint()
        {
            return new VCExprHint(null);
        }

        public string GetMLString()
        {
            if (LemmaToApplyBefore == null)
            {
                return "NONE";
            }
            else
            {
                return "SOME (RewriteVC @{thm " + LemmaToApplyBefore.name + "}" + ")";
            }
        }
            
    }
}