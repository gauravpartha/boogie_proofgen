using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

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
