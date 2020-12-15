using System.Collections;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using ProofGeneration.CFGRepresentation;

namespace ProofGeneration.Passification
{
    public class GlobalVersionChecker
    {
        public static bool CheckVersionMap(
            IDictionary<Variable, int> versionMap,
            PassificationHintManager hintManager,
            IDictionary<Block, IDictionary<Variable, Expr>> initialVarMapping,
            CFGRepr beforePassiveBlocks,
            IDictionary<Block, Block> beforeToPassiveBlocks
        )
        {
           PassiveRelationGen relationGen = new PassiveRelationGen(hintManager, initialVarMapping, beforeToPassiveBlocks, ProofGenLiveVarAnalysis.ComputeLiveVariables(beforePassiveBlocks));
           
           HashSet<Cmd> syncCmds = new HashSet<Cmd>();

           foreach (Block b in beforePassiveBlocks.GetBlocksBackwards())
           {
               relationGen.GenerateVariableRelUpdates(b,
                   beforeToPassiveBlocks[b],
                   beforePassiveBlocks.GetSuccessorBlocks(b),
                   out HashSet<Cmd> newSyncCmds);
               foreach (var cmd in newSyncCmds)
               {
                   syncCmds.Add(cmd);
               }
           }

           return GlobalVersion.CheckIsGlobal(beforeToPassiveBlocks.Values.ToList(), versionMap, beforePassiveBlocks.entry.liveVarsBefore, syncCmds);
        }
    }
}