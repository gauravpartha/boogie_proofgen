﻿using System;

namespace ProofGeneration
{
    class ProofGenUnexpectedStateException<T> : Exception
    {
        Type TriggeringClass
        { get; }

        public ProofGenUnexpectedStateException(Type triggeringClass, string message) : base(message)
        {
            this.TriggeringClass = triggeringClass;
        }

        public ProofGenUnexpectedStateException(Type triggeringClass)
        {
            this.TriggeringClass = triggeringClass;
        }
    }
}
