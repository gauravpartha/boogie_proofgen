using System.Collections.Generic;

namespace ProofGeneration.Isa
{
    public class Proof
    {
        public readonly IList<string> methods; //simple for now

        public Proof(IList<string> methods)
        {
            this.methods = methods;
        }
    }
}