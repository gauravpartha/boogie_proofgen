using Microsoft.Boogie;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace ProofGeneration.BoogieIsaInterface
{
    class BoogieGlobalData
    {
        public IEnumerable<Function> Functions { get; }
        public IEnumerable<Axiom> Axioms { get; }
        public IEnumerable<Variable> GlobalVars { get; }
        public IEnumerable<Variable> Constants { get; }
         
        public BoogieGlobalData(IEnumerable<Function> functions, IEnumerable<Axiom> axioms, IEnumerable<Variable> globalVars, IEnumerable<Variable> constants)
        {
            this.Functions = functions;
            this.Axioms = axioms;
            this.GlobalVars = globalVars;
            this.Constants = constants;
        }

        public static BoogieGlobalData CreateEmpty()
        {
            return new BoogieGlobalData(new List<Function>(), new List<Axiom>(), new List<Variable>(), new List<Variable>());
        }
    }
}
