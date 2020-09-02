using Microsoft.Boogie;
using ProofGeneration.Isa;
using System;

namespace ProofGeneration.VCProofGen
{
    abstract class VCTypeDeclTranslation
    {
        public Term TranslateTypeDecl(Function func)
        {
            string name = func.Name;

            if(name.Equals("type"))
            {
                return Type(func);
            } else if(name.Equals("Ctor"))
            {
                return Ctor(func);
            } else if(name.Equals("intType"))
            {
                return IntType(func);
            } else if(name.Equals("boolType"))
            {
                return BoolType(func);
            } else if(name.Equals("U_2_int"))
            {
                return U2Int(func);
            } else if(name.Equals("U_2_bool"))
            {
                return U2Bool(func);
            } else if(name.Equals("int_2_U"))
            {
                return Int2U(func);
            } else if(name.Equals("bool_2_U"))
            {
                return Bool2U(func);
            } else if(IsTypeConstr(name, out string constrName))
            {
                return TypeConstructor(constrName, func);
            } else if(IsTypeConstrInverse(name, out string invConstrName, out int index))
            {
                return TypeConstructorInverse(invConstrName, index, func);
            } else
            {
                throw new ArgumentException();
            }
        }

        public abstract Term Type(Function func);
        public abstract Term Ctor(Function func);
        public abstract Term IntType(Function func);
        public abstract Term BoolType(Function func);
        public abstract Term U2Int(Function func);
        public abstract Term U2Bool(Function func);
        public abstract Term Int2U(Function func);
        public abstract Term Bool2U(Function func);
        public abstract Term TypeConstructor(string constrName, Function func);
        public abstract Term TypeConstructorInverse(string constrName, int index, Function func);

        private bool IsTypeConstr(string name, out string constrName)
        {
            if (name.EndsWith("Type"))
            {
                string s = name.Substring(0, name.Length - 4);
                if (s.Length > 0)
                {
                    constrName = s;
                    return true;
                }
            }
            constrName = null;
            return false;
        }

        private bool IsTypeConstrInverse(string name, out string constrName, out int index)
        {
            string [] split = name.Split(new string[] { "Inv" }, StringSplitOptions.None);
            if(split.Length == 2)
            {
                if(Int32.TryParse(split[1], out int resIndex) && IsTypeConstr(split[0], out string resConstrName))
                {
                    constrName = resConstrName;
                    index = resIndex;
                    return true;
                }
            }

            constrName = null;
            index = -1;
            return false;
        }

    }
}
