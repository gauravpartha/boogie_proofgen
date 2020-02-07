using System.Collections.Generic;

namespace ProofGeneration
{
    class IsaCommonTypes
    {
        public static TypeIsa getOptionType(TypeIsa elemType)
        {
            return getDataTypeSingle("option", elemType);
        }

        public static TypeIsa getSetType(TypeIsa elemType)
        {
            return getDataTypeSingle("set", elemType);
        }

        public static TypeIsa getListType(TypeIsa elemType)
        {
            return getDataTypeSingle("list", elemType);
        }

        public static TypeIsa getDataTypeSingle(string name, TypeIsa arg)
        {
            var list = new List<TypeIsa>() { arg };
            return new DataType("name", list);
        }

    }
}
