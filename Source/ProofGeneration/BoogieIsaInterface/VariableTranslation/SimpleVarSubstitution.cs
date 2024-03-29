﻿using System;
using System.Collections.Generic;
using Isabelle.Ast;

namespace ProofGeneration.BoogieIsaInterface.VariableTranslation
{
    //TODO support bound variables, might make sense to extract part of DeBruijnTranslation that does this and to re-use the code
    public class SimpleVarSubstitution<T> : IVariableTranslation<T>
    {
        private readonly IDictionary<T, Term> substitution;

        public SimpleVarSubstitution(IDictionary<T, Term> substitution)
        {
            this.substitution = substitution;
        }

        public void AddBoundVariable(T boundVar)
        {
            //TODO
            throw new NotImplementedException();
        }

        public void DropLastBoundVariable()
        {
            //TODO
            throw new NotImplementedException();
        }

        public int NumBoundVariables()
        {
            //TODO
            throw new NotImplementedException();
        }

        public Term TranslateVariable(T variable, out bool isBoundVar)
        {
            isBoundVar = false;
            return substitution[variable];
        }

        public bool TryTranslateVariableId(T variable, out Term id, out bool isBoundVar)
        {
            throw new NotSupportedException();
        }

        public bool TryTranslateVariableIntId(T variable, out int id, out bool isBoundVar)
        {
            throw new NotSupportedException();
        }
    }
}