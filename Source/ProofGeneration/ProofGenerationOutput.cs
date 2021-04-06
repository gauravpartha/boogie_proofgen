using System;
using System.Collections;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Isabelle.Ast;
using Isabelle.IsaPrettyPrint;

namespace ProofGeneration
{
    public static class ProofGenerationOutput
    {
        private static string _mainDir;

        public static void CreateMainDirectory(string fileName)
        {
            if (_mainDir != null)
                throw new ProofGenUnexpectedStateException("main directory already set");
            _mainDir = FreeDirName(Path.GetFileName(fileName) + "_proofs");
            Directory.CreateDirectory(_mainDir);
        }
        
        public static void StoreTheoriesTopLevel(IEnumerable<Theory> theories)
        {
            if (_mainDir == null)
                throw new ProofGenUnexpectedStateException("main directory not yet set");

            foreach (var theory in theories) StoreTheory(_mainDir, theory);
        }
        
        /// <summary>
        /// Stores the provided theories into a new subdirectory with prefix <paramref name="preferredDirName"/>. The
        /// created subdirectory is located in the main proof generation directory used for the current run.
        /// Existing directories or files are not rewritten (i.e., a name that does not clash with any of the existing
        /// directories/files is picked)
        /// </summary>
        /// <param name="preferredDirName">Prefix of new directory.</param>
        /// <param name="theories">Theories to be stored.</param>
        /// <exception cref="ProofGenUnexpectedStateException">Thrown if main proof generation directory is not set.</exception>
        public static void StoreTheoriesInNewDirWithSession(string preferredDirName, IEnumerable<Theory> theories)
        {
            if (_mainDir == null)
                throw new ProofGenUnexpectedStateException("main directory not yet set");

            //create new directory
            var dirPath = Path.Join(_mainDir, FreeDirName(preferredDirName + "_proofs"));
            Directory.CreateDirectory(dirPath);

            foreach (var theory in theories) StoreTheory(dirPath, theory);

            //StoreSessionRoot(dirPath, theories);
        }

        private static string NameWithId(string prefix, int id)
        {
            if (id == 1)
                return prefix;
            return prefix + "_" + id;
        }

        private static string FreeDirName(string preferredName)
        {
            var i = 1;
            while (Directory.Exists(NameWithId(preferredName, i))) i++;

            return NameWithId(preferredName, i);
        }

        private static void StoreTheory(string dirName, Theory theory)
        {
            var path = Path.Combine(dirName, theory.TheoryName + ".thy");
            var sw = new StreamWriter(path);
            var theoryString = IsaPrettyPrinter.PrintTheory(theory);

            sw.WriteLine(theoryString);
            sw.Close();
        }

        private static string ExtractTheoryName(string filename)
        {
            var theoryFile = Path.GetFileName(filename);
            return theoryFile.Remove(theoryFile.Length - 4, 4);
        }

        private static string CombineLinux(string dir, string file)
        {
            return dir + "/" + file;
        }

        public static void FinishStoring()
        {
            if (_mainDir == null)
                throw new ProofGenUnexpectedStateException("main directory not yet set");

            using var sw = new StreamWriter(Path.Combine(_mainDir, "ROOT"));
            sw.WriteLine("session " + Path.GetFileName(_mainDir) + " = " + "Boogie_Lang + ");
            
            var subDirs = Directory.EnumerateDirectories(_mainDir).ToList();
            if (subDirs.Any())
                sw.WriteLine("directories " + String.Join(" ", subDirs.Select(Path.GetFileName)));
    
            sw.WriteLine("theories");
            sw.WriteLine(string.Join(Environment.NewLine,
                Directory.EnumerateFiles(_mainDir).Where(f => f.EndsWith(".thy")).Select(ExtractTheoryName)));
                
            foreach (var subDir in subDirs)
            {
                var subDirName = Path.GetFileName(subDir);
                var theoryFiles = Directory.EnumerateFiles(subDir)
                    .Where(f => f.EndsWith(".thy")).Select(ExtractTheoryName);
                sw.WriteLine(string.Join(Environment.NewLine, theoryFiles.Select(thy => "\""+ CombineLinux(subDirName, thy) + "\"")));
            }
        }

        private static void StoreSessionRoot(string dirPath, IEnumerable<Theory> theories)
        { 
            using var sw = new StreamWriter(Path.Combine(dirPath, "ROOT"));
            sw.WriteLine("session " + Path.GetFileName(dirPath) + " = " + "Boogie_Lang + ");
            sw.WriteLine("theories");
            sw.Write(string.Join(Environment.NewLine, theories.Select(thy => thy.TheoryName)));
            sw.Close();
        }
    }
}