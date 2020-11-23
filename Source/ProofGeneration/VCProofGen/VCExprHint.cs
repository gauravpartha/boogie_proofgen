using System.Collections.Generic;
using System.Linq;
using ProofGeneration.Isa;
using ProofGeneration.IsaML;

namespace ProofGeneration.VCProofGen
{
    public class VCExprHint : INodeML
    {
        //if it is null, then no lemma should be applied, otherwise the lemma should be applied to rewrite the VC expression
        public List<LemmaDecl> LemmaToApplyBefore { get; }

        public VCExprHint(List<LemmaDecl> lemmaToApplyBefore)
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
                var list = LemmaToApplyBefore.Select(lem => "@{thm " + lem.name + "}");
                var listString = "[" + string.Join(",", list) + "]";
                return "SOME (RewriteVC " + listString+ ")";
            }
        }
            
    }
}