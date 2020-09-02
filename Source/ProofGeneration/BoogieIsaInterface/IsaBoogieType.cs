using ProofGeneration.Isa;
using System.Collections.Generic;

namespace ProofGeneration
{
    class IsaBoogieType
    {
        private static readonly TermIdent tprimId = IsaCommonTerms.TermIdentFromName("TPrim");
        private static readonly TermIdent tboolId = IsaCommonTerms.TermIdentFromName("TBool");
        private static readonly TermIdent tintId = IsaCommonTerms.TermIdentFromName("TInt");
        private static readonly TermIdent tvarId = IsaCommonTerms.TermIdentFromName("TVar");
        private static readonly TermIdent tconId = IsaCommonTerms.TermIdentFromName("TCon");

        public static TypeIsa BoogieType()
        {
            return IsaCommonTypes.GetDataTypeNoArg("ty");
        }

        public static Term TVar(int n)
        {
            return new TermApp(tvarId, new NatConst(n));
        }

        public static Term PrimType(Term primType)
        {
            return new TermApp(tprimId, primType);
        }

        public static Term BoolType()
        {
            return tboolId;
        }

        public static Term IntType()
        {
            return tintId;
        }

        public static Term TConType(string constructorName, List<Term> constructorArgs)
        {
            return new TermApp(new TermApp(tconId, new StringConst(constructorName)), new TermList(constructorArgs));
        }

        public static TypeIsa ValType(TypeIsa absValType)
        {
            return new DataType("val", new List<TypeIsa>() { absValType });
        }

        public static TypeIsa AbstractValueTyFunType(TypeIsa absValType)
        {
            return new DataType("absval_ty_fun", new List<TypeIsa>() { absValType });
        }

        public static TypeIsa NormalStateType(TypeIsa absValType)
        {
            return new ArrowType(VnameType(), IsaCommonTypes.GetOptionType(ValType(absValType)));
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

        public static TypeIsa BoogieFuncInterpType(TypeIsa absValType)
        {
            return new ArrowType(IsaCommonTypes.GetListType(BoogieType()), 
                new ArrowType(IsaCommonTypes.GetListType(ValType(absValType)),
                    IsaCommonTypes.GetOptionType(ValType(absValType)))
                    );
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
            return new DataType("var_context", new List<TypeIsa>() { });
        }

        public static TypeIsa FunContextType(TypeIsa absValType)
        {
            return new DataType("fun_context", new List<TypeIsa>() { absValType } );
        }

    }
}
