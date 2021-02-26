using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;

namespace ProofGeneration.BoogieIsaInterface
{
    public class BoogieMethodData
    {
        private readonly BoogieGlobalData globalData;

        public BoogieMethodData(
            BoogieGlobalData globalData,
            IEnumerable<TypeVariable> typeParams,
            IEnumerable<Variable> inParams,
            IEnumerable<Variable> locals,
            IEnumerable<Variable> outParams,
            IEnumerable<IdentifierExpr> modifies,
            IEnumerable<Expr> pres,
            IEnumerable<Expr> posts)
        {
            this.globalData = globalData;
            TypeParams = typeParams;
            InParams = inParams;
            Locals = locals;
            //this.OutParams = outParams;
            ModifiedVars = modifies;
            Preconditions = pres;
            Postconditions = posts;
        }

        public IEnumerable<Function> Functions => globalData.Functions;
        public IEnumerable<Axiom> Axioms => globalData.Axioms;
        public IEnumerable<Variable> GlobalVars => globalData.GlobalVars;
        public IEnumerable<Variable> Constants => globalData.Constants;

        public IEnumerable<TypeVariable> TypeParams { get; }
        public IEnumerable<Variable> InParams { get; }

        public IEnumerable<Variable> Locals { get; }

        //public IEnumerable<Variable> OutParams { get; }
        public IEnumerable<IdentifierExpr> ModifiedVars { get; }
        public IEnumerable<Expr> Preconditions { get; }
        public IEnumerable<Expr> Postconditions { get; }

        public static BoogieMethodData CreateEmpty()
        {
            return new BoogieMethodData(BoogieGlobalData.CreateEmpty(),
                new List<TypeVariable>(),
                new List<Variable>(),
                new List<Variable>(),
                new List<Variable>(),
                new List<IdentifierExpr>(),
                new List<Expr>(),
                new List<Expr>());
        }

        public static BoogieMethodData CreateOnlyGlobal(BoogieGlobalData globalData)
        {
            return new BoogieMethodData(globalData,
                new List<TypeVariable>(),
                new List<Variable>(),
                new List<Variable>(),
                new List<Variable>(),
                new List<IdentifierExpr>(),
                new List<Expr>(),
                new List<Expr>());
        }

        //in the following order: constants then globals then parameters then locals
        public IEnumerable<Variable> AllVariables()
        {
            return Constants.Concat(GlobalVars).Concat(InParams).Concat(Locals);
        }
    }
}