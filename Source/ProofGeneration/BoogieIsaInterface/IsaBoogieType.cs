using ProofGeneration.Isa;
using System.Collections.Generic;

namespace ProofGeneration
{
    class IsaBoogieType
    {
        public static TypeIsa BoogieType()
        {
            return IsaCommonTypes.GetDataTypeNoArg("ty");
        }

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
            return new ArrowType(VnameType(), IsaCommonTypes.GetOptionType(ValType()));
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

        public static TypeIsa VnameType()
        {
            return IsaCommonTypes.GetDataTypeNoArg("vname");
        }

        public static TypeIsa FnameType()
        {
            return IsaCommonTypes.GetDataTypeNoArg("fname");
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
