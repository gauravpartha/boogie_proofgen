using System;

namespace ProofGeneration
{
    class ProofGenUnexpectedStateException : Exception
    {
        Type TriggeringClass
        { get; }

        public ProofGenUnexpectedStateException(Type triggeringClass, string message) : base(message)
        {
            this.TriggeringClass = triggeringClass;
        }

        public ProofGenUnexpectedStateException(string message) : base(message)
        { }
        public ProofGenUnexpectedStateException(Type triggeringClass)
        {
            this.TriggeringClass = triggeringClass;
        }
    }
}
