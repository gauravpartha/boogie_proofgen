//#define PROOFGENACTIVE

using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;
using ProofGeneration.CFGRepresentation;
using ProofGeneration.IsaPrettyPrint;
using ProofGeneration.VCProofGen;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.IO;

namespace ProofGeneration
{
    public class ProofGenerationLayer
    {


        [Conditional("PROOFGENACTIVE")]
        public static void StoreTheory(Implementation impl)
        {
            var programGenerator = new IsaProgramGenerator();
            var cfg = CFGReprTransformer.getCFGRepresentation(impl);
            Theory theory = programGenerator.GetIsaProgram(impl, cfg, impl.Proc.Name);

            var sw = new StreamWriter(impl.Proc.Name + ".thy");

            string theoryString = IsaPrettyPrinter.PrintTheory(theory);

            sw.WriteLine(theoryString);
            sw.Close();
        }

        public static void ConvertVC(VCExpr vc, VCExpressionGenerator gen, Implementation impl)
        {
            VCExpr vcNoLabels = VCExprLabelRemover.RemoveLabels(vc, gen);
            VCExprLet vcNoLabelLet = vcNoLabels as VCExprLet;
            Contract.Assert(vcNoLabelLet != null);

            var cfg = CFGReprTransformer.getCFGRepresentation(impl);

            IDictionary<Block, VCExpr> blockToVCExpr = VCBlockExtractor.BlockToVCMapping(vcNoLabelLet, cfg);            
        }

    }

}
