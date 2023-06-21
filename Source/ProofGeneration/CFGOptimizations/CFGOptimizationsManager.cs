using Isabelle.Ast;
using ProofGeneration.BoogieIsaInterface;
using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using Isabelle.Ast;
using Isabelle.Util;
using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.BoogieIsaInterface.VariableTranslation;
using ProofGeneration.CFGRepresentation;
using ProofGeneration.Util;
using ProofGenUtil;


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
    IDictionary<int, int> CoalescedBlocksToTarget,
    IDictionary<Block, IList<Block>> beforeDagBlockToLoops)
  {
    IDictionary<Block, Block> afterToBefore = beforeToAfter.ToDictionary(x => x.Value, x => x.Key);
    IDictionary<Block, IList<Block>> beforeOptBlockToLoops = new Dictionary<Block, IList<Block>>();
    Block coalescedAfterBlock = new Block();
    
    foreach (Block beforeBlock in beforeOptimizations.GetBlocksForwards())
    {
      if (beforeToAfter.ContainsKey(beforeBlock))
      {
        IList<Block> temp = new List<Block>();
        foreach (Block loopHeader in beforeDagBlockToLoops[beforeToAfter[beforeBlock]])
        {
          temp.Add(afterToBefore[loopHeader]);
        }
        beforeOptBlockToLoops.Add(beforeBlock, temp);
      }
      else if (CoalescedBlocksToTarget.ContainsKey(beforeBlock.UniqueId)) {
        coalescedAfterBlock = GetCoalescedAfterBlock(beforeBlock, beforeToAfter, CoalescedBlocksToTarget);
        List<Block> temp = new List<Block>();
        foreach (Block loopHeader in beforeDagBlockToLoops[coalescedAfterBlock])
        {
          temp.Add(afterToBefore[loopHeader]);
        }

        foreach (Block afterSucc in afterOptimizations.GetSuccessorBlocks(
                   GetCoalescedAfterBlock(beforeBlock, beforeToAfter, CoalescedBlocksToTarget)))
        {
          if (beforeDagBlockToLoops[coalescedAfterBlock].Count < beforeDagBlockToLoops[afterSucc].Count)
          {
            temp.Add(afterToBefore[GetCoalescedAfterBlock(beforeBlock, beforeToAfter, CoalescedBlocksToTarget)]);
            break;
          }
        }
        beforeOptBlockToLoops.Add(beforeBlock, temp);
      }
    }
    
    
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
    //TODO: Check Dead Variables Elimination (Variables names change as well). See DeadVarElim.blp
    //TODO: Check document names (not always p_before_cfg_to_dag_prog and p_unoptimized_cfg_prog)
    
    
    CFGRepr beforeOptimizationsCopy = beforeOptimizations.Copy(); //TODO: extend it to deep copy, not sure how to do that
    beforeOptimizationsCopy.DeleteBackedges(beforeOptBlockToLoops);

    for (int i = 0; i < beforeOptimizationsCopy.NumOfBlocks(); i++)
    {
      Block current = GetBlockWithoutSuccessor(beforeOptimizationsCopy);
      Block beforeBlock = FindBlock(beforeOptimizations, current.UniqueId);
      
      if (isLoopHead(beforeBlock, beforeOptimizations, beforeOptBlockToLoops, beforeToAfter) && CoalescedBlocksToTarget.ContainsKey(beforeBlock.UniqueId)) //In this case we have a coalesced loop head
      {
        coalescedAfterBlock = GetCoalescedAfterBlock(beforeBlock, beforeToAfter, CoalescedBlocksToTarget);
        var globalBlock = lemmaManager.LoopHeadCoalesced(beforeBlock, coalescedAfterBlock,
          bigblock => GetGlobalBlockLemmaName(bigblock, lemmaNamer),
          bigblock => GetHybridBlockLemmaName(bigblock, lemmaNamer),
          beforeOptBlockToLoops[beforeBlock]);
        outerDecls.Add(globalBlock);
      } 
      else if (isLoopHead(beforeBlock, beforeOptimizations, beforeOptBlockToLoops,beforeToAfter)) //normal Loop Head
      {
        var globalBlock = lemmaManager.LoopHeadNotCoalesced(beforeBlock, beforeToAfter[beforeBlock], bigblock => GetGlobalBlockLemmaName(bigblock, lemmaNamer), beforeOptBlockToLoops, beforeOptBlockToLoops[beforeBlock]);
        outerDecls.Add(globalBlock);
      }
      else if (CoalescedBlocksToTarget.ContainsKey(beforeBlock.UniqueId)) //in this case we have block coalescing
      {
        if (ProgramToVCProof.LemmaHelper.FinalStateIsMagic(beforeBlock)) //Pruning of Unreachable Blocks Coalesced
        {
          coalescedAfterBlock = GetCoalescedAfterBlock(beforeBlock, beforeToAfter, CoalescedBlocksToTarget);
          var pruningCoalesced = lemmaManager.HybridBlockLemmaPruning(beforeBlock, coalescedAfterBlock,
            bigblock => GetHybridBlockLemmaName(bigblock, lemmaNamer), beforeOptBlockToLoops[beforeBlock]);
          outerDecls.Add(pruningCoalesced);
        }
        else if (beforeToAfter.ContainsKey(beforeBlock)) //Head of coalesced blocks
        {
          Block afterBlock = beforeToAfter[beforeBlock];
          var head = lemmaManager.HybridBlockLemma(beforeBlock, afterBlock,
            beforeOptimizations.GetSuccessorBlocks(beforeBlock).FirstOrDefault(),
            bigblock => GetGlobalBlockLemmaName(bigblock, lemmaNamer),
            bigblock => GetHybridBlockLemmaName(bigblock, lemmaNamer), beforeOptBlockToLoops[beforeBlock]);
          outerDecls.Add(head);
          var convertGlobalBlock = lemmaManager.ConvertHybridToGlobal(beforeBlock, afterBlock,
            bigblock => GetGlobalBlockLemmaName(bigblock, lemmaNamer),
            bigblock => GetHybridBlockLemmaName(bigblock, lemmaNamer), beforeOptBlockToLoops[beforeBlock]);
          outerDecls.Add(convertGlobalBlock);
        }
        else if (beforeOptimizations.GetSuccessorBlocks(beforeBlock).Count() != 1 || beforeOptimizations.GetSuccessorBlocks(beforeBlock).First().Predecessors.Count() != 1) //tail of coalesced blocks
        {
          coalescedAfterBlock = GetCoalescedAfterBlock(beforeBlock, beforeToAfter, CoalescedBlocksToTarget);
          
          var tail = lemmaManager.HybridBlockLemmaTail(beforeBlock, coalescedAfterBlock,
            bigblock => GetGlobalBlockLemmaName(bigblock, lemmaNamer),
            bigblock => GetHybridBlockLemmaName(bigblock, lemmaNamer), 
            beforeOptBlockToLoops, beforeOptBlockToLoops[beforeBlock]);
          outerDecls.Add(tail);
        }
        else //in Between Block
        {
          coalescedAfterBlock = GetCoalescedAfterBlock(beforeBlock, beforeToAfter, CoalescedBlocksToTarget);
          var inBetweenBlock = lemmaManager.HybridBlockLemma(beforeBlock, coalescedAfterBlock,
            beforeOptimizations.GetSuccessorBlocks(beforeBlock).FirstOrDefault(),
            bigblock => GetGlobalBlockLemmaName(bigblock, lemmaNamer),
            bigblock => GetHybridBlockLemmaName(bigblock, lemmaNamer), beforeOptBlockToLoops[beforeBlock]);
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
            var pruning = lemmaManager.GlobalBlockLemmaPruningNotCoalesced(beforeBlock, afterBlock, GetGlobalBlockLemmaName(beforeBlock, lemmaNamer), beforeOptBlockToLoops[beforeBlock]);
            outerDecls.Add(pruning);
          }
          else //otherwhise we just need to apply the normal global block lemma. Assumption: Global Block Lemma holds for all successors
          {
            var globalBlock = lemmaManager.GlobalBlockLemma(beforeBlock, afterBlock, bigblock => GetGlobalBlockLemmaName(bigblock, lemmaNamer), beforeOptBlockToLoops, beforeOptBlockToLoops[beforeBlock]);
            outerDecls.Add(globalBlock);
          }
        }
      }
      beforeOptimizationsCopy.DeleteBlock(current);
    }
    

    
    
    /*
    foreach (Block beforeBlock in beforeOptimizations.GetBlocksForwards())
    {
      if (isLoopHead(beforeBlock, beforeOptimizations, beforeOptBlockToLoops, beforeToAfter) && CoalescedBlocksToTarget.ContainsKey(beforeBlock.UniqueId)) //In this case we have a coalesced loop head
      {
        coalescedAfterBlock = GetCoalescedAfterBlock(beforeBlock, beforeToAfter, CoalescedBlocksToTarget);
        var globalBlock = lemmaManager.LoopHeadCoalesced(beforeBlock, coalescedAfterBlock,
          bigblock => GetGlobalBlockLemmaName(bigblock, lemmaNamer),
          bigblock => GetHybridBlockLemmaName(bigblock, lemmaNamer),
          beforeOptBlockToLoops[beforeBlock]);
        outerDecls.Add(globalBlock);
      } 
      else if (isLoopHead(beforeBlock, beforeOptimizations, beforeOptBlockToLoops,beforeToAfter)) //normal Loop Head
      {
        var globalBlock = lemmaManager.LoopHeadNotCoalesced(beforeBlock, beforeToAfter[beforeBlock], bigblock => GetGlobalBlockLemmaName(bigblock, lemmaNamer), beforeOptBlockToLoops, beforeOptBlockToLoops[beforeBlock]);
        outerDecls.Add(globalBlock);
      }
      else if (CoalescedBlocksToTarget.ContainsKey(beforeBlock.UniqueId)) //in this case we have block coalescing
      {
        if (ProgramToVCProof.LemmaHelper.FinalStateIsMagic(beforeBlock)) //Pruning of Unreachable Blocks Coalesced
        {
          coalescedAfterBlock = GetCoalescedAfterBlock(beforeBlock, beforeToAfter, CoalescedBlocksToTarget);
          var pruningCoalesced = lemmaManager.HybridBlockLemmaPruning(beforeBlock, coalescedAfterBlock,
            bigblock => GetHybridBlockLemmaName(bigblock, lemmaNamer), beforeOptBlockToLoops[beforeBlock]);
          outerDecls.Add(pruningCoalesced);
        }
        else if (beforeToAfter.ContainsKey(beforeBlock)) //Loop head
        {
          Block afterBlock = beforeToAfter[beforeBlock];
          var head = lemmaManager.HybridBlockLemma(beforeBlock, afterBlock,
            beforeOptimizations.GetSuccessorBlocks(beforeBlock).FirstOrDefault(),
            bigblock => GetGlobalBlockLemmaName(bigblock, lemmaNamer),
            bigblock => GetHybridBlockLemmaName(bigblock, lemmaNamer), beforeOptBlockToLoops[beforeBlock]);
          outerDecls.Add(head);
          var convertGlobalBlock = lemmaManager.ConvertHybridToGlobal(beforeBlock, afterBlock,
            bigblock => GetGlobalBlockLemmaName(bigblock, lemmaNamer),
            bigblock => GetHybridBlockLemmaName(bigblock, lemmaNamer), beforeOptBlockToLoops[beforeBlock]);
          outerDecls.Add(convertGlobalBlock);
        }
        else if (beforeOptimizations.GetSuccessorBlocks(beforeBlock).Count() != 1 || beforeOptimizations.GetSuccessorBlocks(beforeBlock).First().Predecessors.Count() != 1)
        {
          coalescedAfterBlock = GetCoalescedAfterBlock(beforeBlock, beforeToAfter, CoalescedBlocksToTarget);
          
          var tail = lemmaManager.HybridBlockLemmaTail(beforeBlock, coalescedAfterBlock,
            bigblock => GetGlobalBlockLemmaName(bigblock, lemmaNamer),
            bigblock => GetHybridBlockLemmaName(bigblock, lemmaNamer), 
            beforeOptBlockToLoops, beforeOptBlockToLoops[beforeBlock]);
          outerDecls.Add(tail);
        }
        else //in Between Block
        {
          coalescedAfterBlock = GetCoalescedAfterBlock(beforeBlock, beforeToAfter, CoalescedBlocksToTarget);
          var inBetweenBlock = lemmaManager.HybridBlockLemma(beforeBlock, coalescedAfterBlock,
            beforeOptimizations.GetSuccessorBlocks(beforeBlock).FirstOrDefault(),
            bigblock => GetGlobalBlockLemmaName(bigblock, lemmaNamer),
            bigblock => GetHybridBlockLemmaName(bigblock, lemmaNamer), beforeOptBlockToLoops[beforeBlock]);
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
            var pruning = lemmaManager.GlobalBlockLemmaPruningNotCoalesced(beforeBlock, afterBlock, GetGlobalBlockLemmaName(beforeBlock, lemmaNamer), beforeOptBlockToLoops[beforeBlock]);
            outerDecls.Add(pruning);
          }
          else //otherwhise we just need to apply the normal global block lemma. Assumption: Global Block Lemma holds for all successors
          {
            var globalBlock = lemmaManager.GlobalBlockLemma(beforeBlock, afterBlock, bigblock => GetGlobalBlockLemmaName(bigblock, lemmaNamer), beforeOptBlockToLoops, beforeOptBlockToLoops[beforeBlock]);
            outerDecls.Add(globalBlock);
          }
        }
      }
    }
    */
    
    
    

    List<string> importTheories = new List<string>
    {
      "Boogie_Lang.Semantics", "Boogie_Lang.Util", "Boogie_Lang.CFGOptimizationsLoop",
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
  
  private static bool isLoopHead(Block b, CFGRepr beforeOptimizations, IDictionary<Block, IList<Block>> beforeOptBlockToLoops, IDictionary<Block, Block> beforeToAfter)
  {
    foreach (Block succ in beforeOptimizations.GetSuccessorBlocks(b))
    {
      if (beforeOptBlockToLoops[b].Count < beforeOptBlockToLoops[succ].Count && beforeToAfter.ContainsKey(b))
      {
        return true;
      }
    }
    return false;
  }

  private static Block GetBlockWithoutSuccessor(CFGRepr cfg)
  {
    foreach (Block curr in cfg.GetBlocksForwards())
    {
      if (cfg.GetSuccessorBlocks(curr).Count() == 0)
      {
        return curr;
      }
    }
    return null;
  }
  
  private static void RemoveBlock(CFGRepr cfg, Block remove)
  {
    
  }
  
  private static Block FindBlock(CFGRepr cfg, int id)
  {
    foreach (Block curr in cfg.GetBlocksForwards())
    {
      if (curr.UniqueId == id)
      {
        return curr;
      }
    }
    return null;
  }

  
}