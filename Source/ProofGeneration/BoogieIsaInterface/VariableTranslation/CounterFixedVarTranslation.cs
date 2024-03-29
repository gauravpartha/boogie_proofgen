﻿using System;
using System.Collections.Generic;
using Microsoft.Boogie;

namespace ProofGeneration.BoogieIsaInterface.VariableTranslation
{
    /// <summary>
    ///     Gives unique names to variables (identified by the corresponding object, not the name).
    /// </summary>
    public class CounterFixedVarTranslation : IFixedVariableTranslation<Variable>
    {
        private readonly Dictionary<Variable, int> nameToId = new Dictionary<Variable, int>();

        private int nextId;

        public int VariableId(Variable v)
        {
            if (nameToId.TryGetValue(v, out var result)) return result;

            result = nextId;
            nameToId.Add(v, result);
            nextId++;
            return result;
        }

        public string OutputMapping()
        {
            return string.Join(Environment.NewLine, nameToId);
        }
    }
}