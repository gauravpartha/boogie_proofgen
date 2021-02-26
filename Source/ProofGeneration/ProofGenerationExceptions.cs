using System;

namespace ProofGeneration
{
    internal class ProofGenUnexpectedStateException : Exception
    {
        public ProofGenUnexpectedStateException(Type triggeringClass, string message) : base(message)
        {
            TriggeringClass = triggeringClass;
        }

        public ProofGenUnexpectedStateException(string message) : base(message)
        {
        }

        public ProofGenUnexpectedStateException(Type triggeringClass)
        {
            TriggeringClass = triggeringClass;
        }

        private Type TriggeringClass { get; }
    }
}