using ProofGeneration.Isa;
using System.Collections.Generic;

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

        public static TypeIsa ValType()
        {
            return new DataType("val", new List<TypeIsa>());
        }

        public static TypeIsa NormalStateType()
        {
            return new ArrowType(IsaCommonTypes.GetDataTypeNoArg("vname"), IsaCommonTypes.GetOptionType(ValType()));
        }

        public static TypeIsa StateType()
        {
            return IsaCommonTypes.GetDataTypeNoArg("state");
        }

        public static TypeIsa GetCFGNodeType()
        {
            return new DataType("node", new List<TypeIsa>());
        }

        public static TypeIsa GetBlockType()
        {
            return new DataType("block", new List<TypeIsa>());
        }

        public static TypeIsa BoogieFuncInterpType()
        {
            return new ArrowType(IsaCommonTypes.GetListType(ValType()), IsaCommonTypes.GetOptionType(ValType()));
        }

        public static TypeIsa VarContextType()
        {
            return new DataType("var_context", new List<TypeIsa>());
        }

        public static TypeIsa FunContextType()
        {
            return new DataType("fun_context", new List<TypeIsa>());
        }

    }
}
