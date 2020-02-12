//#define PROOFGENACTIVE

using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;
using ProofGeneration.CFGRepresentation;
using ProofGeneration.Isa;
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

            StoreTheory(theory);
        }

        public static void ConvertVC(VCExpr vc, VCExpressionGenerator gen, Program p, Implementation impl)
        {
           
            LocaleDecl locale = VCToIsaInterface.ConvertVC(vc, gen, p, impl);
            var theory = new Theory("vc_" + impl.Proc.Name,
                new List<string> { "Main" },
                new List<OuterDecl> { locale });

            StoreTheory(theory);
        }

        private static void StoreTheory(Theory theory)
        {
            var sw = new StreamWriter(theory.theoryName + ".thy");

            string theoryString = IsaPrettyPrinter.PrintTheory(theory);

            sw.WriteLine(theoryString);
            sw.Close();
        }

    }

}
