using System;
using Microsoft.Boogie;
using ProofGeneration.Isa;

namespace ProofGeneration.VCProofGen
{
    internal abstract class VCTypeDeclTranslation
    {
        public bool TryTranslateTypeDecl(Function func, out Term result)
        {
            var name = func.Name;

            if (name.Equals("type"))
            {
                result = Type(func);
            }
            else if (name.Equals("Ctor"))
            {
                result = Ctor(func);
            }
            else if (name.Equals("intType"))
            {
                result = IntType(func);
            }
            else if (name.Equals("boolType"))
            {
                result = BoolType(func);
            }
            else if (name.Equals("U_2_int"))
            {
                result = U2Int(func);
            }
            else if (name.Equals("U_2_bool"))
            {
                result = U2Bool(func);
            }
            else if (name.Equals("int_2_U"))
            {
                result = Int2U(func);
            }
            else if (name.Equals("bool_2_U"))
            {
                result = Bool2U(func);
            }
            else if (IsTypeConstr(name, out var constrName))
            {
                result = TypeConstructor(constrName, func);
            }
            else if (IsTypeConstrInverse(name, out var invConstrName, out var index))
            {
                result = TypeConstructorInverse(invConstrName, index, func);
            }
            else
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
                var s = name.Substring(0, name.Length - 4);
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
            var split = name.Split(new[] {"Inv"}, StringSplitOptions.None);
            if (split.Length == 2)
                if (int.TryParse(split[1], out var resIndex) && IsTypeConstr(split[0], out var resConstrName))
                {
                    constrName = resConstrName;
                    index = resIndex;
                    return true;
                }

            constrName = null;
            index = -1;
            return false;
        }
    }
}