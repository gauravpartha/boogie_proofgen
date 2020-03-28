using Microsoft.Boogie;
using ProofGeneration.CFGRepresentation;
using ProofGeneration.Util;
using System.Collections.Generic;

namespace ProofGeneration.ProgramToVCProof
{
    public static class ConstantPropInformation
    {
        //return information at beginning of each block and store information at end of each block in out parameter
        //only store information if it is live
        public static IDictionary<Block, IDictionary<Variable, Expr>> ConstantVariableInformation(CFGRepr cfg, out IDictionary<Block, IDictionary<Variable, Expr>> constantExit)
        {
            var constantEntry = new Dictionary<Block, IDictionary<Variable, Expr>>();
            constantExit = new Dictionary<Block, IDictionary<Variable, Expr>>();
            foreach (Block b in cfg.GetBlocksForwards())
            {
                var bEntry = constantEntry.ContainsKey(b) ? constantEntry[b] : null;
                var bExit = ConstantExit(b, bEntry);
                constantExit.Add(b, bExit);
                foreach (Block bSucc in cfg.GetSuccessorBlocks(b))
                {
                    //propagate constant information
                    if (constantEntry.TryGetValue(bSucc, out IDictionary<Variable, Expr> succEntry))
                    {
                        //bSucc has multiple predecessors --> consolidate constant information
                        constantEntry[bSucc] = Consolidate(bExit, succEntry);
                    }
                    else
                    {
                        constantEntry.Add(bSucc, bExit);
                    }
                }
            }
            return constantEntry;
        }

        private static IDictionary<Variable, Expr> Consolidate(IDictionary<Variable, Expr> constantInfoBlock, IDictionary<Variable, Expr> succConstantInfo)
        {
            var result = new Dictionary<Variable, Expr>();

            foreach (var varAndExpr in constantInfoBlock)
            {
                Variable v = varAndExpr.Key;
                Expr exp = varAndExpr.Value;

                if (succConstantInfo.TryGetValue(v, out Expr otherExp))
                {
                    if (exp is LiteralExpr && otherExp is LiteralExpr && exp.Equals(otherExp))
                    {
                        result.Add(v, exp);
                    }
                    else if (exp is IdentifierExpr idExp && otherExp is IdentifierExpr otherIdExp && idExp.Decl.Equals(otherIdExp.Decl))
                    {
                        result.Add(v, exp);
                    }
                }
            }
            return result;
        }

        private static IDictionary<Variable, Expr> ConstantExit(Block b, IDictionary<Variable, Expr> constantEntry)
        {
            var result = constantEntry != null ? new Dictionary<Variable, Expr>(constantEntry)
                                               : new Dictionary<Variable, Expr>();

            foreach (Cmd cmd in b.Cmds)
            {
                if (cmd is AssignCmd assignCmd)
                {

                    assignCmd.Lhss.ZipDo(assignCmd.Rhss,
                        (lhs, rhs) =>
                        {
                            if (lhs is SimpleAssignLhs simpleLhs)
                            {
                                Variable leftVar = simpleLhs.AssignedVariable.Decl;
                                if (rhs is IdentifierExpr rhsId)
                                {
                                    //check if rhs variable is constant, if so propagate that information
                                    if (result.TryGetValue(rhsId.Decl, out Expr rhsConstant))
                                    {
                                        result[leftVar] = rhsConstant;
                                    }
                                    else
                                    {
                                        result[leftVar] = rhs;
                                    }
                                }
                                else if (rhs is LiteralExpr)
                                {
                                    result[leftVar] = rhs;
                                } else
                                {
                                    //rhs is not constant --> remove constant information
                                    result.Remove(leftVar);
                                }
                            }
                        });
                }
                else if (cmd is HavocCmd havocCmd)
                {
                    foreach (IdentifierExpr ie in havocCmd.Vars)
                    {
                        result.Remove(ie.Decl);
                    }
                }
            }

            return result;
        }
    }
}
