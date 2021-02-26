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
            PassiveRelationGen relationGen,
            CFGRepr beforePassiveBlocks,
            IDictionary<Block, Block> beforeToPassiveBlocks
        )
        {
            return GlobalVersion.CheckIsGlobal(beforeToPassiveBlocks.Values.ToList(), relationGen, versionMap,
                relationGen.LiveVarsBeforeBlock(beforePassiveBlocks.entry));
        }
    }
}