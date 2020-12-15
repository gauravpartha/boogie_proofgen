using System;
using System.Collections;
using System.Collections.Generic;
using System.Runtime.CompilerServices;
using Microsoft.Boogie;

namespace ProofGeneration.Passification
{
    public class PassiveRelationGen
    {
        private readonly PassificationHintManager hintManager;
        private readonly IDictionary<Block, IDictionary<Variable,Expr>> initialVarMapping;
        private readonly IDictionary<Block, Block> newToOrigCopy;
        
        public PassiveRelationGen(PassificationHintManager hintManager, 
            IDictionary<Block, IDictionary<Variable,Expr>> initialVarMapping,
            IDictionary<Block, Block> newToOrigCopy)
        {
            this.hintManager = hintManager;
            this.initialVarMapping = initialVarMapping;
            this.newToOrigCopy = newToOrigCopy;
        }

        public List<Tuple<Variable, Expr>> GenerateStateRelation(Block nonPassiveBlock)
        { 
            var initMappingBlock = initialVarMapping[newToOrigCopy[nonPassiveBlock]];

            var result = new List<Tuple<Variable, Expr>>();

            foreach (Variable liveVar in nonPassiveBlock.liveVarsBefore)
            {
                if (initMappingBlock.TryGetValue(liveVar, out Expr passiveExpr))
                {
                    result.Add(Tuple.Create(liveVar, passiveExpr));
                }
                else
                {
                    //variable is live but has not been assigned to yet --> corresponding passive variable is the same one
                    result.Add(Tuple.Create(liveVar, (Expr) new IdentifierExpr(null, liveVar)));
                }
            }

            return result;
        }

        public List<Tuple<Variable, Expr, bool>> GenerateVariableRelUpdates(
            Block nonPassiveBlock,
            Block passiveBlock,
            IEnumerable<Block> nonPassiveSuccessors,
            out HashSet<Cmd> syncCmds)
        {
            return GenerateVariableRelUpdates(nonPassiveBlock, passiveBlock, nonPassiveSuccessors,
                hintManager.GetHint(nonPassiveBlock), out syncCmds);
        }
        
        private List<Tuple<Variable, Expr, bool>> GenerateVariableRelUpdates(
            Block nonPassiveBlock, 
            Block passiveBlock,
            IEnumerable<Block> nonPassiveSuccessors,
            IEnumerable<PassificationHint> hints,
            out HashSet<Cmd> syncCmds)
        {
            var result = new List<Tuple<Variable, Expr, bool>>();
            syncCmds = new HashSet<Cmd>();

            using (var hintsEnumerator = hints.GetEnumerator())
            {
                bool CheckHintsConsistent(Cmd cmd, Variable variable, PassificationHint hint) => hint.OrigVar == variable;
                
                //side effect: moves hints enumerator 
                Action<Cmd, Variable> checkNextHint = (cmd, variable) =>
                {
                    if (!hintsEnumerator.MoveNext())
                        throw new ProofGenUnexpectedStateException(typeof(PassiveRelationGen),
                            "Passification hints not in-sync");

                    if (!CheckHintsConsistent(cmd, variable, hintsEnumerator.Current))
                        throw new ProofGenUnexpectedStateException(typeof(PassiveRelationGen),
                            "Passification hints not in-sync");
                };
                    
                using (var nonPassiveEnumerator = nonPassiveBlock.cmds.GetEnumerator())
                using (var passiveEnumerator = passiveBlock.cmds.GetEnumerator())
                {
                    while (nonPassiveEnumerator.MoveNext())
                    {
                        Cmd nonPassiveCmd = nonPassiveEnumerator.Current;

                        if (nonPassiveCmd is AssignCmd assignCmd)
                        {
                            checkNextHint(assignCmd, assignCmd.Lhss[0].DeepAssignedVariable);

                            if (!(assignCmd.Rhss[0] is LiteralExpr _) && !(assignCmd.Rhss[0] is IdentifierExpr _))
                            {
                                result.Add(Tuple.Create(hintsEnumerator.Current.OrigVar, hintsEnumerator.Current.PassiveExpr, false));
                               //no constant propagation: we expect an assume command
                                if(!passiveEnumerator.MoveNext() || !(passiveEnumerator.Current is AssumeCmd))
                                    throw new ProofGenUnexpectedStateException(typeof(PassiveRelationGen),
                                        "No matching passive cmd for assignment");
                            }
                            else
                            {
                                //constant propagation
                                result.Add(Tuple.Create(hintsEnumerator.Current.OrigVar, hintsEnumerator.Current.PassiveExpr, true));
                            }
                        }
                        else if (nonPassiveCmd is HavocCmd havocCmd)
                        {
                            foreach (IdentifierExpr id in havocCmd.Vars)
                            {
                                checkNextHint(havocCmd, id.Decl);
                                result.Add(Tuple.Create(hintsEnumerator.Current.OrigVar, hintsEnumerator.Current.PassiveExpr, false));
                            }
                        }
                        else if (nonPassiveCmd is AssumeCmd _ || nonPassiveCmd is AssertCmd _)
                        {
                            if(!passiveEnumerator.MoveNext())
                                throw new ProofGenUnexpectedStateException(typeof(PassiveRelationGen),
                                    "No matching passive cmd for assignment");
                        }
                        else
                        {
                            throw new NotImplementedException();
                        }
                    }

                    if (hintsEnumerator.MoveNext())
                    {
                        throw new ProofGenUnexpectedStateException(typeof(PassiveRelationGen),
                            "Too many hints.");
                    }
                    
                    /* We have covered all commands in the non-passive commands. The remaining passive commands must be
                       synchronization commands.
                     */
                    while (passiveEnumerator.MoveNext())
                    {
                        Cmd passiveCmd = passiveEnumerator.Current;
                        if (IsSynchronizationCommand(passiveCmd, out var lhs, out _))
                        {
                            /* Need to figure out what is corresponding original variable in the non-passive program.
                               For this, we look at the incarnation map in the successors, which should map the original
                               variable to the left hand side variable of the currently inspected command 
                             */
                            syncCmds.Add(passiveCmd);
                            
                            Variable origVar = null;
                            foreach (var succ in nonPassiveSuccessors)
                            {
                                var succVarMapping = initialVarMapping[newToOrigCopy[succ]];
                                foreach (var varExprPair in succVarMapping)
                                {
                                    if (varExprPair.Value is IdentifierExpr ie && ie.Decl.Equals(lhs.Decl))
                                    {
                                        origVar = varExprPair.Key;
                                        break;
                                    }
                                }
                                if (origVar != null)
                                    break;
                            }
                            if(origVar == null)
                                throw new ProofGenUnexpectedStateException(GetType(),"Could not find original variable for synchronization assumption.");
                            
                            result.Add(Tuple.Create(origVar, (Expr) lhs, false));
                        }
                        else
                        {
                            throw new ProofGenUnexpectedStateException(typeof(PassiveRelationGen), 
                                "Passification: expected sync-command");
                        }
                    }
                }
            }
            
            return result;
        }

        private static bool IsSynchronizationCommand(Cmd cmd, out IdentifierExpr lhs, out Expr rhs)
        {
            if (cmd is AssumeCmd assumeCmd)
            {
                if (assumeCmd.Expr is NAryExpr nary && nary.Fun is BinaryOperator bop && bop.Op.Equals(BinaryOperator.Opcode.Eq))
                {
                    if (nary.Args[0] is IdentifierExpr ieLeft)
                    {
                        if (nary.Args[1] is IdentifierExpr ieRight)
                        {
                            lhs = ieLeft;
                            rhs = ieRight;
                            return true;
                        }

                        if (nary.Args[1] is LiteralExpr lit)
                        {
                            lhs = ieLeft;
                            rhs = lit;
                            return true;
                        }
                    }
                }
            }

            lhs = null;
            rhs = null;
            return false;
        }
    }
}