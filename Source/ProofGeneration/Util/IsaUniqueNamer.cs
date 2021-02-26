using System.Collections.Generic;
using System.Text.RegularExpressions;
using Microsoft.Boogie.VCExprAST;

namespace ProofGeneration.Util
{
    public class IsaUniqueNamer
    {
        private readonly List<char> illegalChars;

        private readonly HashSet<string> reservedNames;

        private readonly string spacer;
        private readonly UniqueNamer uniqueNamer;

        public IsaUniqueNamer(string spacer)
        {
            this.spacer = spacer;
            uniqueNamer = new UniqueNamer
            {
                Spacer = spacer
            };
            reservedNames = new HashSet<string>();
            reservedNames.Add("A"); //value to abstract value map
            reservedNames.Add("abs");

            illegalChars = new List<char>();
            illegalChars.Add('@');
        }

        public IsaUniqueNamer() : this("AA")
        {
        }

        public string GetName(object obj, string preferredName)
        {
            var preferredNameMod = preferredName;
            foreach (var illegalChar in illegalChars) preferredNameMod = preferredNameMod.Replace(illegalChar, '_');

            if (reservedNames.Contains(preferredNameMod)) preferredNameMod = preferredNameMod + "ZZ";
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
            var firstChar = new Regex("^[A-Za-z]");

            var sMod = s;

            if (!firstChar.IsMatch(s))
                sMod = "isa" + spacer + s;

            var illegalCharacters = new Regex("[@#^*!&]");

            return illegalCharacters.Replace(sMod, spacer);
        }
    }
}