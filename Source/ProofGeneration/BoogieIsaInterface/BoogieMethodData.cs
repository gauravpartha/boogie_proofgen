using System.Collections.Generic;

using Microsoft.Boogie;

namespace ProofGeneration.BoogieIsaInterface
{
    class BoogieMethodData
    {
        private readonly BoogieGlobalData globalData;

        public IEnumerable<Function> Functions { get { return globalData.Functions; } }
        public IEnumerable<Axiom> Axioms { get { return globalData.Axioms; } }
        public IEnumerable<Variable> GlobalVars { get { return globalData.GlobalVars; } }
        public IEnumerable<Variable> Constants { get { return globalData.Constants; } }

        public IEnumerable<Variable> InParams { get; }
        public IEnumerable<Variable> Locals { get; }
        public IEnumerable<Variable> OutParams { get; }

        public BoogieMethodData(
            BoogieGlobalData globalData, 
            IEnumerable<Variable> inParams, 
            IEnumerable<Variable> locals,
            IEnumerable<Variable> outParams)
        {
            this.globalData = globalData;
            this.InParams = inParams;
            this.Locals = locals;
            this.OutParams = outParams;
        }
    }
}
