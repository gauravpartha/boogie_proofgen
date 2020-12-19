using System.Collections.Generic;
using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.CFGRepresentation;

namespace ProofGeneration.Passification
{
    /// <summary>
    /// Live variable analysis used for passification proof generation
    /// The analysis differs from Boogie's standard live variable analysis. Assignments that are dead do not kill
    /// the variables on the RHS. 
    /// </summary>
    public class ProofGenLiveVarAnalysis
    {

        //cfg must be acyclic
        public static IDictionary<Block, IEnumerable<Variable>> ComputeLiveVariables(CFGRepr cfg, BoogieMethodData methodData)
        {
            var liveVarsBefore = new Dictionary<Block, IEnumerable<Variable>>();

            var allVarsSet = new HashSet<Variable>(methodData.AllVariables());

            foreach (Block b in cfg.GetBlocksBackwards())
            {
                HashSet<Variable> bCurLiveVars =  new HashSet<Variable>();
                foreach (var bSuc in cfg.GetSuccessorBlocks(b))
                {
                    bCurLiveVars.UnionWith(liveVarsBefore[bSuc]);
                }
                
                for(int idx = b.cmds.Count - 1; idx >= 0; idx--)
                {
                   UpdateLiveSet(b.cmds[idx], bCurLiveVars); 
                }

                //due to the VariableCollector's implementation bound variables may also have been included
                bCurLiveVars.RemoveWhere(v => !allVarsSet.Contains(v));
                liveVarsBefore.Add(b, bCurLiveVars);
            }

            return liveVarsBefore;
        }

        private static void UpdateLiveSet(Cmd cmd, HashSet<Variable> liveVars)
        {
            if (cmd is AssignCmd assignCmd)
            {
                foreach (var lhs in assignCmd.Lhss)
                {
                    liveVars.Remove(lhs.DeepAssignedVariable);
                }

                foreach (var rhs in assignCmd.Rhss)
                {
                    VariableCollector  collector = new VariableCollector();
                    collector.Visit(rhs);
                    //we neglect that the corresponding lhs may be dead
                    liveVars.UnionWith(collector.usedVars);
                }
            } else if (cmd is HavocCmd havocCmd)
            {
                foreach (var ie in havocCmd.Vars)
                {
                    liveVars.Remove(ie.Decl);
                }
            } else if (cmd is PredicateCmd predicateCmd)
            {
                //live set is not cleared when reaching "assert false" or "assume false"
                VariableCollector  collector = new VariableCollector();
                collector.Visit(predicateCmd.Expr);
                liveVars.UnionWith(collector.usedVars);
            }
            else
            {
                throw new ProofGenUnexpectedStateException("Unsupported command in program right before passification.");
            }
        }
        
    }
}