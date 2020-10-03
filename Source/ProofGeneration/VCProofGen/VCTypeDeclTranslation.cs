using Microsoft.Boogie;
using ProofGeneration.Isa;
using System;

namespace ProofGeneration.VCProofGen
{
    abstract class VCTypeDeclTranslation
    {
        public bool TryTranslateTypeDecl(Function func, out Term result)
        {
            string name = func.Name;

            if(name.Equals("type"))
            {
                result = Type(func);
            } else if(name.Equals("Ctor"))
            {
                result = Ctor(func);
            } else if(name.Equals("intType"))
            {
                result = IntType(func);
            } else if(name.Equals("boolType"))
            {
                result = BoolType(func);
            } else if(name.Equals("U_2_int"))
            {
                result = U2Int(func);
            } else if(name.Equals("U_2_bool"))
            {
                result = U2Bool(func);
            } else if(name.Equals("int_2_U"))
            {
                result = Int2U(func);
            } else if(name.Equals("bool_2_U"))
            {
                result = Bool2U(func);
            } else if(IsTypeConstr(name, out string constrName))
            {
                result = TypeConstructor(constrName, func);
            } else if(IsTypeConstrInverse(name, out string invConstrName, out int index))
            {
                result = TypeConstructorInverse(invConstrName, index, func);
            } else
            {
                result = null;
                return false;
            }

            return true;
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
