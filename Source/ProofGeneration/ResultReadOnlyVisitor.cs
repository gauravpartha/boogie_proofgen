using Microsoft.Boogie;
using System.Collections.Generic;
using System.Diagnostics.Contracts;

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
            Contract.Assert(TranslatePrecondition(node));
            Visit(node);
            return Results.Pop();
        }

        protected void ReturnResult(T result)
        {
            Results.Push(result);
        }
    }
}
