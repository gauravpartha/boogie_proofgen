﻿using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using Microsoft.Boogie;

namespace ProofGeneration
{
    /** visitor where visited nodes uses results from children */
    abstract class ResultReadOnlyVisitor<T> : ReadOnlyVisitor
    {
        protected Stack<T> Results { get; } = new Stack<T>();

        public bool StateIsFresh()
        {
            return Results.Count == 0;
        }

        abstract protected bool TranslatePrecondition(Absy node);

        public T Translate(Absy node)
        {
            Contract.Requires(TranslatePrecondition(node));
            Visit(node);
            return Results.Pop();
        }

        protected void ReturnResult(T result)
        {
            Results.Push(result);
        }
    }
}
