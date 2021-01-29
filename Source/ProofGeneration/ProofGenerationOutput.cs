using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using ProofGeneration.Isa;
using ProofGeneration.IsaPrettyPrint;

namespace ProofGeneration
{
    public class ProofGenerationOutput
    {
       
        private static string mainDir = null;

        public static void CreateMainDirectory(string fileName)
        {
            if(mainDir != null)
                throw new ProofGenUnexpectedStateException("main directory already set");
            mainDir = FreeDirName(Path.GetFileName(fileName) + "_proofs" );
            Directory.CreateDirectory(mainDir);
        }
        
        public static void StoreProofs(string name, IEnumerable<Theory> theories)
        {
            
            if(mainDir == null)
                throw new ProofGenUnexpectedStateException("main directory not yet set");
            
            //create new directory
            string dirPath = Path.Join(mainDir, FreeDirName(name+"_proofs"));
            Directory.CreateDirectory(dirPath);

            foreach (var theory in theories)
            {
               StoreTheory(dirPath, theory); 
            }
            
            StoreSessionRoot(dirPath, theories);
        }

        private static string NameWithId(string prefix, int id)
        {
            if (id == 1)
                return prefix;
            else
                return prefix + "_" + id;
        } 

        private static string FreeDirName(string preferredName)
        {
            int i = 1;
            while (Directory.Exists(NameWithId(preferredName,i)))
            {
                i++;
            }

            return NameWithId(preferredName, i);
        }

        private static void StoreTheory(string dirName, Theory theory)
        {
            string path = Path.Combine(dirName, theory.theoryName +".thy");
            var sw = new StreamWriter(path);
            string theoryString = IsaPrettyPrinter.PrintTheory(theory);

            sw.WriteLine(theoryString);
            sw.Close();
        }

        private static void StoreSessionRoot(string dirPath, IEnumerable<Theory> theories)
        {
           var sw = new StreamWriter(Path.Combine(dirPath, "ROOT"));
           sw.WriteLine("session " + Path.GetFileName(dirPath) + " = " + "Boogie_Lang + ");
           sw.WriteLine("theories");
           sw.Write(String.Join(Environment.NewLine, theories.Select(thy => thy.theoryName)));
           sw.Close();
        }
    }
}