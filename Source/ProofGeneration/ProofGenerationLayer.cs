using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using Microsoft.Boogie;

namespace ProofGeneration
{
    public class ProofGenerationLayer
    {

        public static void StoreTheory(Implementation impl)
        {
            var programGenerator = new IsaProgramGenerator();
            Theory theory = programGenerator.GetIsaProgram(impl, impl.Proc.Name);

            var sw = new StreamWriter(impl.Proc.Name + ".thy");

            string theoryString = IsaPrettyPrinter.PrintTheory(theory);

            sw.WriteLine(theoryString);
            sw.Close();
        }

    }
}
