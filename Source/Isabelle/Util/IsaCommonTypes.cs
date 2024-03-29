﻿using System.Collections.Generic;
using Isabelle.Ast;

namespace Isabelle.Util
{
    public static class IsaCommonTypes
    {
        public static TypeIsa GetUnitType()
        {
            return GetDataTypeNoArg("unit");
        }

        public static TypeIsa GetOptionType(TypeIsa elemType)
        {
            return GetDataTypeSingle("option", elemType);
        }

        public static TypeIsa GetSetType(TypeIsa elemType)
        {
            return GetDataTypeSingle("set", elemType);
        }

        public static TypeIsa GetListType(TypeIsa elemType)
        {
            return GetDataTypeSingle("list", elemType);
        }

        public static TypeIsa GetDataTypeSingle(string name, TypeIsa arg)
        {
            var list = new List<TypeIsa> {arg};
            return new DataType(name, list);
        }

        public static TypeIsa GetDataTypeNoArg(string name)
        {
            return new DataType(name, new List<TypeIsa>());
        }
    }
}