using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;
using System.Threading.Tasks;

namespace ProofGeneration.Util
{
    public class IsaUniqueNamer
    {
        private readonly Microsoft.Boogie.VCExprAST.UniqueNamer uniqueNamer;

        private readonly string spacer;

        private readonly HashSet<string> reservedNames;
        private readonly List<char> illegalChars;

        public IsaUniqueNamer(string spacer)
        {
            this.spacer = spacer;
            uniqueNamer = new Microsoft.Boogie.VCExprAST.UniqueNamer()
            {
                Spacer = spacer
            };
            reservedNames = new HashSet<string>();
            reservedNames.Add("A"); //value to abstract value map

            illegalChars = new List<char>();
            illegalChars.Add('@');
        }

        public IsaUniqueNamer() : this("_") { }

        public string GetName(object obj, string preferredName)
        {
            var preferredNameMod = preferredName;
            foreach (var illegalChar in illegalChars)
            {
                preferredNameMod = preferredNameMod.Replace(illegalChar, '_');
            }

            if (reservedNames.Contains(preferredNameMod))
            {
                preferredNameMod = preferredNameMod + "ZZ";
            }
            return uniqueNamer.GetName(obj, GetValidIsaString(preferredNameMod));
        }

        public string GetLocalName(object obj, string preferredName)
        {
            return uniqueNamer.GetLocalName(obj, GetValidIsaString(preferredName));
        }

        public void PushScope()
        {
            uniqueNamer.PushScope();
        }

        public void PopScope()
        {
            uniqueNamer.PopScope();
        }
        
        private string GetValidIsaString(string s)
        {
            Regex firstChar = new Regex("^[A-Za-z]");

            string sMod = s;

            if (!firstChar.IsMatch(s))
                sMod = "isa" + spacer + s;

            Regex illegalCharacters = new Regex("[@#^*!&]");            

            return illegalCharacters.Replace(sMod, spacer);
        }

    }
}
