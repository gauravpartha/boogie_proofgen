using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;

namespace ProofGeneration.BoogieIsaInterface
{
    public class BoogieMethodData
    {
        private readonly BoogieGlobalData globalData;

        public IEnumerable<Function> Functions => globalData.Functions;
        public IEnumerable<Axiom> Axioms => globalData.Axioms;
        public IEnumerable<Variable> GlobalVars => globalData.GlobalVars;
        public IEnumerable<Variable> Constants => globalData.Constants;

        public IEnumerable<TypeVariable> TypeParams { get; }
        public IEnumerable<Variable> InParams { get; }
        public IEnumerable<Variable> Locals { get; }
        //public IEnumerable<Variable> OutParams { get; }
        public IEnumerable<IdentifierExpr> ModifiedVars { get; }
        public IEnumerable<Requires> Preconditions { get; }
        public IEnumerable<Ensures> Postcondtions { get; }

        public BoogieMethodData(
            BoogieGlobalData globalData,
            IEnumerable<TypeVariable> typeParams,
            IEnumerable<Variable> inParams, 
            IEnumerable<Variable> locals,
            IEnumerable<Variable> outParams,
            IEnumerable<IdentifierExpr> modifies,
            IEnumerable<Requires> pres,
            IEnumerable<Ensures> posts)
        {
            this.globalData = globalData;
            this.TypeParams = typeParams;
            this.InParams = inParams;
            this.Locals = locals;
            //this.OutParams = outParams;
            this.ModifiedVars = modifies;
            this.Preconditions = pres;
            this.Postcondtions = posts;
        }

        public static BoogieMethodData CreateEmpty()
        {
            return new BoogieMethodData(BoogieGlobalData.CreateEmpty(),
                new List<TypeVariable>(),
                new List<Variable>(),
                new List<Variable>(),
                new List<Variable>(),
                new List<IdentifierExpr>(),
                new List<Requires>(),
                new List<Ensures>());
        }

        public static BoogieMethodData CreateOnlyGlobal(BoogieGlobalData globalData)
        {
            return new BoogieMethodData(globalData,
                new List<TypeVariable>(),
                new List<Variable>(),
                new List<Variable>(),
                new List<Variable>(),
                new List<IdentifierExpr>(),
                new List<Requires>(),
                new List<Ensures>());
        }

        //in the following order: constants then globals then parameters then locals
        public IEnumerable<Variable> AllVariables()
        {
            return Constants.Concat(GlobalVars).Concat(Locals).Concat(InParams);
        }
    }
}