using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace ProofGeneration
{
    class IsaBoogieType
    {
        public static Term BoolType()
        {
            return IsaCommonTerms.TermIdentFromName("TBool");
        }

        public static Term IntType()
        {
            return IsaCommonTerms.TermIdentFromName("TInt");
        }

        public static TypeIsa getCFGNodeType()
        {
            return new DataType("node", new List<TypeIsa>());
        }

        public static TypeIsa getBlockType()
        {
            return new DataType("block", new List<TypeIsa>());
        }

    }
}
