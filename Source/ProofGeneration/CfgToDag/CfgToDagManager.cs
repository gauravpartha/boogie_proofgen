using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.BoogieIsaInterface.VariableTranslation;
using ProofGeneration.CFGRepresentation;
using ProofGeneration.Isa;
using ProofGeneration.Util;

namespace ProofGeneration.CfgToDag
{
    public class CfgToDagManager
    {
        
        /**
         * cases:
         * 1) is loop head block
         * 2) is back edge block
         * 3) successor is loop head block
         *
         * any combination is possible
         */
        public static Theory CfgToDagProof(
            string theoryName,
            CFGRepr beforeDagCfg,
            CFGRepr afterDagCfg,
            CfgToDagHintManager hintManager,
            IDictionary<Block,Block> beforeToAfter,
            IProgramAccessor beforeDagProgAccess,
            IProgramAccessor afterDagProgAccess,
            IVariableTranslationFactory varFactory)
        {
            IDictionary<Block, Block> afterToBefore = beforeToAfter.ToDictionary(x => x.Value, x => x.Key);
            
            //track mapping from blocks to loops that the block is contained in
            IDictionary<Block, IList<Block>> blocksToLoops = new Dictionary<Block, IList<Block>>();

            foreach (Block afterBlock in afterDagCfg.GetBlocksBackwards())
            {
                if (afterToBefore.TryGetValue(afterBlock, out Block beforeBlock))
                {
                    HashSet<Block> loops = new HashSet<Block>();
                    foreach (var bSuc in beforeDagCfg.GetSuccessorBlocks(beforeBlock))
                    {
                        if (blocksToLoops.TryGetValue(bSuc, out var loopsSuc))
                        {
                            //if successor inside of a loop L and the block is not the loop head of L, then the block is also inside L
                            foreach (var loopSuc in loopsSuc)
                            {
                                if (!loopSuc.Equals(beforeBlock))
                                {
                                    loops.Add(loopSuc);
                                } 
                            }
                        }
                    }
                    //a node is inside all loops for which it has an out-going backedge 
                    if(hintManager.TryIsBackedgeNode(beforeBlock, out var backedgeLoops))
                    {
                        foreach (var backedgeLoop in backedgeLoops)
                        {
                            loops.Add(backedgeLoop);
                        }
                    }

                    var loopsList = loops.ToList();
                    blocksToLoops.Add(beforeBlock, loopsList);
                }
            }

            string varContextName = "\\<Lambda>1";
            var varContextAbbrev = new AbbreviationDecl(
                varContextName,
                new Tuple<IList<Term>, Term>(new List<Term>(), beforeDagProgAccess.VarContext())
                );
            
            
            CfgToDagLemmaManager lemmaManager = new CfgToDagLemmaManager(
                beforeDagProgAccess, 
                afterDagProgAccess, 
                afterDagCfg,
                varContextName, 
                hintManager,
                blocksToLoops,
                beforeToAfter,
                varFactory);
            
            var lemmaNamer = new IsaUniqueNamer();
            var outerDecls = new List<OuterDecl>();
            
            outerDecls.Add(varContextAbbrev);
            outerDecls.Add(new DeclareDecl("Nat.One_nat_def[simp del]"));
            
            foreach (Block afterBlock in afterDagCfg.GetBlocksBackwards())
            {
                if (afterToBefore.TryGetValue(afterBlock, out Block beforeBlock))
                {
                    //if the node's only edge is a backedge, then an "assume false" will be added
                    bool singleCutEdge = hintManager.TryIsBackedgeNode(beforeBlock, out List<Block> _) &&
                                         beforeDagCfg.NumOfSuccessors(beforeBlock) == 1;
                    
                    var (localLemmas, cfgLemma) = 
                        lemmaManager.BlockLemma(
                        beforeBlock, 
                        afterBlock, 
                        beforeDagCfg.GetSuccessorBlocks(beforeBlock),
                        block => GetLemmaName(block, lemmaNamer),
                        block => GetCfgLemmaName(block, lemmaNamer),
                        singleCutEdge
                        );
                    
                    outerDecls.AddRange(localLemmas);
                    outerDecls.Add(cfgLemma);
                }
                else
                {
                   //block was added as part of transformation 
                   if (afterBlock.Label.Contains("PreconditionGeneratedEntry"))
                   {
                       //TODO 
                       continue;
                   }

                   var afterBlockSuccessors = afterDagCfg.GetSuccessorBlocks(afterBlock);
                   if (afterBlockSuccessors.Count() == 0)
                   {
                       //must be the generated unified exit block --> TODO handle this
                       continue;
                   }
                   
                   if (afterBlockSuccessors.Count() != 1)
                   {
                      throw new ProofGenUnexpectedStateException("Block added in CFG-to-DAG phase does not have a unique successor"); 
                   }
                   
                   var afterUniqueSuc = afterBlockSuccessors.First();
                   if (afterToBefore.TryGetValue(afterUniqueSuc, out Block beforeUniqueSuc))
                   {
                       var lemma = lemmaManager.NewBlockLemma(
                           GetCfgLemmaName(afterBlock, lemmaNamer),
                           afterBlock,
                           afterUniqueSuc,
                           beforeUniqueSuc
                       );
                       outerDecls.Add(lemma);
                   }
                   else
                   {
                       throw new ProofGenUnexpectedStateException("CFG-to-DAG: Unique successor of added block cannot be mapped to original block");
                   }
                }
            }
            
            return new Theory(
                theoryName,
                new List<string> { "Boogie_Lang.Semantics", "Boogie_Lang.Util", "Boogie_Lang.BackedgeElim", beforeDagProgAccess.TheoryName(), 
                                    afterDagProgAccess.TheoryName() },
                outerDecls
                );
        }
        
        private static string GetLemmaName(Block b, IsaUniqueNamer namer)
        { 
            return namer.GetName(b, "block_" + b.Label);
        }
        
        private static string GetCfgLemmaName(Block b, IsaUniqueNamer namer)
        { 
            return "cfg_"+namer.GetName(b, "block_" + b.Label);
        }
    }
}