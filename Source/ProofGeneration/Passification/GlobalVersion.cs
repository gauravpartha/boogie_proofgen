using System;
using System.Collections;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Boogie.GraphUtil;
using ProofGeneration.CFGRepresentation;
using ProofGeneration.Util;

namespace ProofGeneration.Passification
{
    public class GlobalVersion
    {

        private HashSet<Block> _versionedBlocks;
        private IDictionary<Variable, int> _versionMap;

        private int _nextVersion = 0;

        private enum CaseType {
            Undefined, Case1 ,Case2
        };
        
        public IDictionary<Variable, int> GlobalVersionMap(IEnumerable<Variable> entryVariables, Block entry, IList<Block> blocks)
        {
            _versionedBlocks = new HashSet<Block>();
            _versionMap = new Dictionary<Variable , int>();
            _nextVersion = 0;
            foreach (var entryVar in entryVariables)
            {
                VersionVariable(entryVar);
            }

            var queue = new List<Block>();
            
            Graph<Block> graph = GraphUtil.GraphFromBlocks(blocks);
            
            //TODO: make the currently inefficient computation more efficient
            queue.Add(entry);

            while (queue.Any())
            {
                /* find next block B where all predecessors have been marked and where one of the following two cases hold
                 * (Case 1) B is the only predecessor of all of B's successors
                 * (Case 2) B has a single successor with multiple predecessors ps and each block in ps only has marked
                 *      predecessors
                 */

                Block blockToHandle = null;
                CaseType caseId = CaseType.Undefined;
                
                foreach (var block in queue)
                {
                    if (IsUniquePredecessor(block, graph))
                    {
                        blockToHandle = block;
                        caseId = CaseType.Case1;
                        break;
                    } else if (ReadySynchronization(block, graph))
                    {
                        blockToHandle = block;
                        caseId = CaseType.Case2;
                        break;
                    }
                }
                
                if(blockToHandle == null || caseId == CaseType.Undefined)
                    throw new ProofGenUnexpectedStateException(GetType(), "Could not compute global version map.");

                List<Block> nextNodes = null;
                if (caseId == CaseType.Case1)
                {
                    nextNodes = HandleCase1(blockToHandle, graph).ToList(); 
                }
                else
                {
                    nextNodes = HandleCase2(blockToHandle, graph).ToList();
                }

                queue.RemoveAll(b => _versionedBlocks.Contains(b));
                queue.AddRange(nextNodes);
                if (nextNodes.Any(b => _versionedBlocks.Contains(b)))
                {
                   throw new ProofGenUnexpectedStateException(GetType(), "Added already versioned block to queue"); 
                }
            }

            return _versionMap;
        }

        public static bool CheckIsGlobal(
            IList<Block> blocks,
            IDictionary<Variable, int> versionMap,
            IEnumerable<Variable> entryVars,
            HashSet<Cmd> isSyncStmt)
        {
            var largestVersion = new Dictionary<Block, int>();
            var markedVars = new HashSet<Variable>(entryVars);
            var graph = GraphUtil.GraphFromBlocks(blocks);

            var sortedNodes = graph.TopologicalSort();

            var maxVersionInitVars = entryVars.Any() ? entryVars.Select(v => versionMap[v]).Max() : -1;
            
            foreach (Block b in sortedNodes)
            {

                var predecessors = graph.Predecessors(b).ToList();
                int maxVersionPred;
                if (predecessors.Any())
                {
                    maxVersionPred = graph.Predecessors(b).Select(b => largestVersion[b]).Max();
                }
                else
                {
                    maxVersionPred = maxVersionInitVars;
                }

                bool correct = findLargestVersion(b, versionMap, maxVersionPred, markedVars, isSyncStmt, out int maxVersionBlock);
                if (!correct)
                    return false;
                largestVersion.Add(b, maxVersionBlock);
            }

            return true;
        }

        public static bool findLargestVersion(
            Block b, 
            IDictionary<Variable, int> versionMap, 
            int maxVersionPred, 
            HashSet<Variable> markedVars, 
            HashSet<Cmd> isSyncStmt,
            out int maxVersion)
        {
            maxVersion = maxVersionPred;
            foreach (var cmd in b.Cmds)
            {
                if (cmd is AssumeCmd assumeCmd)
                {
                     if (assumeCmd.Expr is NAryExpr nary && nary.Fun is BinaryOperator bop && bop.Op.Equals(BinaryOperator.Opcode.Eq))
                     {
                         if (nary.Args[0] is IdentifierExpr ieLeft)
                         {
                             var lhs = ieLeft.Decl;
                             if (isSyncStmt.Contains(assumeCmd) || !markedVars.Contains(lhs))
                             {
                                 //lhs is a new variable
                                 if (versionMap[lhs] <= maxVersionPred)
                                 {
                                     return false;
                                 }

                                 markedVars.Add(lhs);
                                 maxVersion = Math.Max(versionMap[lhs], maxVersion);
                             }
                         }
                     }
                }
            }

            return true;
        }
        
        private IEnumerable<Block> HandleCase1(Block b, Graph<Block> graph)
        {
            VersionBlock(b);
            return graph.Successors(b);
        }

        private IEnumerable<Block> HandleCase2(Block b, Graph<Block> graph)
        {
            var uniqueSuc = graph.Successors(b).First();
            foreach (var preSuc in uniqueSuc.Predecessors)
            {
                VersionBlock(preSuc);
            }

            return new List<Block> {uniqueSuc};
        }
        

        private void VersionBlock(Block b)
        {
            /* new variables can only be variables on the left hand side of an equality assumption (but need not be) */
            foreach (var cmd in b.Cmds)
            {
                if (cmd is AssumeCmd assumeCmd)
                {
                     if (assumeCmd.Expr is NAryExpr nary && nary.Fun is BinaryOperator bop && bop.Op.Equals(BinaryOperator.Opcode.Eq))
                     {
                         if (nary.Args[0] is IdentifierExpr ieLeft)
                         {
                             VersionVariable(ieLeft.Decl);
                         }
                     }                   
                }
            }
            _versionedBlocks.Add(b);
        }

        private void VersionVariable(Variable v)
        {
             if (!_versionMap.ContainsKey(v))
             {
                 //lhs is a new variable
                 _versionMap.Add(v, _nextVersion);
                 _nextVersion++;
             }
        }
        
        private bool IsUniquePredecessor(Block b, Graph<Block> graph)
        {
            var successors = graph.Successors(b);

            return successors.All(suc => graph.Predecessors(suc).Count() == 1);
        }

        private bool ReadySynchronization(Block b, Graph<Block> graph)
        {
            var successors = graph.Successors(b).ToList();
            if (successors.Count != 1)
            {
                return false;
            }

            var uniqueSuc = successors.First();
            var preSuc = graph.Predecessors(uniqueSuc);

            return 
                preSuc.All(pre => graph.Predecessors(pre).
                All(prepre => _versionedBlocks.Contains(prepre) ));
        }
    }
}