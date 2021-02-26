using System.Collections.Generic;
using System.Diagnostics.Contracts;
using Microsoft.Boogie;

namespace ProofGeneration
{
    /**
     * visitor where visited nodes uses results from children
     */
    public abstract class ResultReadOnlyVisitor<T> : ReadOnlyVisitor
    {
        protected Stack<T> Results { get; } = new Stack<T>();

        public bool StateIsFresh()
        {
            return Results.Count == 0;
        }

        protected abstract bool TranslatePrecondition(Absy node);

        public T Translate(Absy node)
        {
            if (!StateIsFresh()) throw new ProofGenUnexpectedStateException(GetType());
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