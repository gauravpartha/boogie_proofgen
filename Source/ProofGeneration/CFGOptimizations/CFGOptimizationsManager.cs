using Isabelle.Ast;
using ProofGeneration.BoogieIsaInterface;
using System;
using System.Collections.Generic;
using System.Linq;
using Isabelle.Ast;
using Isabelle.Util;
using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.BoogieIsaInterface.VariableTranslation;
using ProofGeneration.CFGRepresentation;
using ProofGeneration.Util;



namespace ProofGeneration.CFGOptimizations;

public class CfgOptimizationsManager
{

  //string uniqueTheoryName,
  //PhasesTheories phasesTheories,
  public static Theory CfgOptProof(
    PhasesTheories phasesTheories,
    CFGRepr beforeOptimizations,
    CFGRepr afterOptimizations,
    IDictionary<Block, Block> beforeToAfter, // mapping from current block to target block
    IProgramAccessor beforeOptCfgProgAcccess, //before CFG optimizations
    IProgramAccessor afterOptCfgProgAccess, //after CFG optimizationsList<(Block, Block)> CoalescedBlocks
    IDictionary<int, List <int>> ListCoalescedBlocks, //TODO: Optimize CFGOptimizationsLemmaManager by using this dictionary
    IDictionary<int, int> CoalescedBlocksToTarget)
  {
    
    var varContextName = "\\<Lambda>";
    var varContextAbbrev = new AbbreviationDecl(
      varContextName,
      new Tuple<IList<Term>, Term>(new List<Term>(), afterOptCfgProgAccess.VarContext()));
    
    var funContextWfName = "Wf_Fun";


    var lemmaManager = new CFGOptimizationsLemmaManager(
      beforeOptCfgProgAcccess,
      afterOptCfgProgAccess,
      beforeOptimizations,
      afterOptimizations,
      funContextWfName,
      beforeToAfter); //TODO: Add necessary declarations

    var lemmaNamer = new IsaUniqueNamer();
    var outerDecls = new List<OuterDecl>();
    
    
    outerDecls.Add(varContextAbbrev);
    outerDecls.Add(new DeclareDecl("Nat.One_nat_def[simp del]"));
    List<string> proofMethods = new List<string>();
    Block coalescedAfterBlock = new Block();
    //assumption: no loops
    foreach (Block beforeBlock in beforeOptimizations.GetBlocksForwards())
    {
      if (CoalescedBlocksToTarget.ContainsKey(beforeBlock.UniqueId)) //in this case we have block coalescing
      {
        if (ProgramToVCProof.LemmaHelper.FinalStateIsMagic(beforeBlock)) //Pruning of Unreachable Blocks Coalesced
        {
          coalescedAfterBlock = GetCoalescedAfterBlock(beforeBlock, beforeToAfter, CoalescedBlocksToTarget);
          var pruningCoalesced = lemmaManager.HybridBlockLemmaPruning(beforeBlock, coalescedAfterBlock,
            bigblock => GetHybridBlockLemmaName(bigblock, lemmaNamer));
          outerDecls.Add(pruningCoalesced);
        }
        else if (beforeToAfter.ContainsKey(beforeBlock)) //head
        {
          Block afterBlock = beforeToAfter[beforeBlock];
          var head = lemmaManager.HybridBlockLemma(beforeBlock, afterBlock,
            beforeOptimizations.GetSuccessorBlocks(beforeBlock).FirstOrDefault(),
            bigblock => GetGlobalBlockLemmaName(bigblock, lemmaNamer),
            bigblock => GetHybridBlockLemmaName(bigblock, lemmaNamer));
          outerDecls.Add(head);
          var convertGlobalBlock = lemmaManager.ConvertHybridToGlobal(beforeBlock, afterBlock,
            bigblock => GetGlobalBlockLemmaName(bigblock, lemmaNamer),
            bigblock => GetHybridBlockLemmaName(bigblock, lemmaNamer));
          outerDecls.Add(convertGlobalBlock);
        }
        else if (beforeOptimizations.GetSuccessorBlocks(beforeBlock).Count() != 1 || beforeOptimizations.GetSuccessorBlocks(beforeBlock).First().Predecessors.Count() != 1) //tail
        {
          coalescedAfterBlock = GetCoalescedAfterBlock(beforeBlock, beforeToAfter, CoalescedBlocksToTarget);
          
          var tail = lemmaManager.HybridBlockLemmaTail(beforeBlock, coalescedAfterBlock,
            bigblock => GetGlobalBlockLemmaName(bigblock, lemmaNamer),
            bigblock => GetHybridBlockLemmaName(bigblock, lemmaNamer));
          outerDecls.Add(tail);
        }
        else //in Between Block
        {
          coalescedAfterBlock = GetCoalescedAfterBlock(beforeBlock, beforeToAfter, CoalescedBlocksToTarget);
          var inBetweenBlock = lemmaManager.HybridBlockLemma(beforeBlock, coalescedAfterBlock,
            beforeOptimizations.GetSuccessorBlocks(beforeBlock).FirstOrDefault(),
            bigblock => GetGlobalBlockLemmaName(bigblock, lemmaNamer),
            bigblock => GetHybridBlockLemmaName(bigblock, lemmaNamer));
          outerDecls.Add(inBetweenBlock);
        }
      }
      else //no block coalescing
      {
        if (beforeToAfter.Keys.Contains(beforeBlock))
        {
          Block afterBlock = beforeToAfter[beforeBlock];
          if (ProgramToVCProof.LemmaHelper.FinalStateIsMagic(beforeBlock)) //If there is an assume or assert false statement in the block
          {
            var pruning = lemmaManager.GlobalBlockLemmaPruningNotCoalesced(beforeBlock, afterBlock, GetGlobalBlockLemmaName(beforeBlock, lemmaNamer));
            outerDecls.Add(pruning);
          }
          else //otherwhise we just need to apply the normal global block lemma. Assumption: Global Block Lemma holds for all successors
          {
            var globalBlock = lemmaManager.GlobalBlockLemma(beforeBlock, afterBlock, bigblock => GetGlobalBlockLemmaName(bigblock, lemmaNamer));
            outerDecls.Add(globalBlock);
          }
        }
      }
      
    }

    List<string> importTheories = new List<string>
    {
      "Boogie_Lang.Semantics", "Boogie_Lang.Util", "Boogie_Lang.CFGOptimizations", "Boogie_Lang.CFGOptimizationsLoop",
      afterOptCfgProgAccess.TheoryName(),
      beforeOptCfgProgAcccess.TheoryName()
    };
    
    return new Theory(
      phasesTheories.TheoryName(PhasesTheories.Phase.CfgOptimizations),
      importTheories,
      outerDecls
    ); 
  }
  
  private static string GetGlobalBlockLemmaName(Block b, IsaUniqueNamer namer)
  {
    return "global_block_lemma_" + namer.GetName(b, "block_" + b.Label);
  }
  
  private static string GetHybridBlockLemmaName(Block b, IsaUniqueNamer namer)
  {
    return "hybrid_block_lemma_" + namer.GetName(b, "block_" + b.Label);
  }

  private static Block GetCoalescedAfterBlock(Block b, IDictionary<Block, Block> beforeToAfter, IDictionary<int, int> CoalescedBlocksToTarget)
  {
    foreach (Block beforeBlockNew in beforeToAfter.Keys) //Get the Coalesced After Block
    {
      if (beforeToAfter[beforeBlockNew].UniqueId == CoalescedBlocksToTarget[b.UniqueId])
      {
        return beforeToAfter[beforeBlockNew];
      }
    }
    return null;
  }

  
}