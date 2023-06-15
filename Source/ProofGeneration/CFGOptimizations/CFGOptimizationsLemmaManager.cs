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


namespace ProofGeneration.CFGOptimizations;

public class CFGOptimizationsLemmaManager
{
  private readonly IProgramAccessor beforeOptProgAccess;
  private readonly IProgramAccessor afterOptProgAccess;
  private readonly CFGRepr beforeOptimizations;
  private readonly CFGRepr afterOptimizations;
  private readonly string funContextWfName;
  private readonly IDictionary<Block, Block> beforeToAfterBlock;
  public CFGOptimizationsLemmaManager(
    IProgramAccessor beforeOptProgAccess,
    IProgramAccessor afterOptProgAccess,
    CFGRepr beforeOptimizations,
    CFGRepr afterOptimizations,
    string funContextWfName,
    IDictionary<Block, Block> beforeToAfterBlock
  )
  {
    this.beforeOptProgAccess = beforeOptProgAccess;
    this.afterOptProgAccess = afterOptProgAccess;
    this.beforeOptimizations = beforeOptimizations;
    this.afterOptimizations = afterOptimizations;
    this.funContextWfName = funContextWfName;
    this.beforeToAfterBlock = beforeToAfterBlock;
  }

  public LemmaDecl GlobalBlockLemmaPruningNotCoalesced( //Pruning of unreachable blocks where no coalescing happened
    Block beforeBlock,
    Block afterBlock,
    string blockLemmaName,
    IList<Block> Loops)
  {
    var proofMethods = new List<string>
    {
      
      "apply (rule pruning_not_coalesced_loop)",
      "apply (rule p_unoptimized_cfg_prog.outEdges_" + beforeOptProgAccess.BlockInfo().BlockIds[beforeBlock] + ")",
      "apply (rule p_before_cfg_to_dag_prog.node_" + afterOptProgAccess.BlockInfo().BlockIds[afterBlock] + ")",
      "apply (rule p_unoptimized_cfg_prog.node_" + beforeOptProgAccess.BlockInfo().BlockIds[beforeBlock]  + ")",
      "apply (unfold p_unoptimized_cfg_prog.block_" + beforeOptProgAccess.BlockInfo().BlockIds[beforeBlock]  + "_def)",
      "apply simp",
      "apply (unfold p_before_cfg_to_dag_prog.block_" + afterOptProgAccess.BlockInfo().BlockIds[afterBlock] + "_def)",
      "by simp"
    };
    
    var loopHeads = new List<string>();
    foreach (Block loop in Loops)
    {
      loopHeads.Add("(" + beforeOptProgAccess.BlockInfo().BlockIds[loop] + "," + afterOptProgAccess.BlockInfo().BlockIds[beforeToAfterBlock[loop]] + ")");
    }
    
    var varContextName = "\\<Lambda>";
    IList<Term> terms = new List<Term>();
    terms.Add(IsaCommonTerms.TermIdentFromName("A"));
    terms.Add(IsaCommonTerms.TermIdentFromName("M"));
    terms.Add(IsaCommonTerms.TermIdentFromName(varContextName));
    terms.Add(IsaCommonTerms.TermIdentFromName("\\<Gamma>"));
    terms.Add(IsaCommonTerms.TermIdentFromName("\\<Omega>"));
    terms.Add(IsaCommonTerms.TermIdentFromName("p_unoptimized_cfg_prog.proc_body"));
    terms.Add(IsaCommonTerms.TermIdentFromName("p_before_cfg_to_dag_prog.proc_body"));
    terms.Add(new NatConst(beforeOptProgAccess.BlockInfo().BlockIds[beforeBlock]));
    terms.Add(new NatConst(afterOptProgAccess.BlockInfo().BlockIds[afterBlock]));
    terms.Add(IsaCommonTerms.TermIdentFromName("{" + string.Join(",", loopHeads) + "}"));
    Term conclusion = new TermApp(IsaCommonTerms.TermIdentFromName("global_block_lemma_loop"), terms);


    var blockLemma = new LemmaDecl(
      blockLemmaName, 
      conclusion,
      new Proof(proofMethods));
    return blockLemma;
  }

  public LemmaDecl GlobalBlockLemma( //normal global block lemma where the global block lemma needs to hold for all successors
    Block beforeBlock,
    Block afterBlock,
    Func<Block, string> blockLemmaName,
    IDictionary<Block, IList<Block>> beforeOptBlockToLoops,
    IList<Block> Loops)
  {
    var loopHeads = new List<string>();
    foreach (Block loop in Loops)
    {
      loopHeads.Add("(" + beforeOptProgAccess.BlockInfo().BlockIds[loop] + "," + afterOptProgAccess.BlockInfo().BlockIds[beforeToAfterBlock[loop]] + ")");
    }
    
    var function = new List<string>();
    foreach (Block succ in beforeOptimizations.GetSuccessorBlocks(beforeBlock))
    {
      if (beforeToAfterBlock.Keys.Contains(succ))
      {
        Block succAfter = beforeToAfterBlock[succ];
        function.Add("(" + beforeOptProgAccess.BlockInfo().BlockIds[succ] + "," + afterOptProgAccess.BlockInfo().BlockIds[succAfter] + ")");
      }
    }
    var proofMethods = new List<string>
    {
      "apply (rule loopBlock_global_block[where ?f = \"the ∘ map_of [" + string.Join(",", function) + "]\"])",
      "apply (rule p_unoptimized_cfg_prog.outEdges_" + beforeOptProgAccess.BlockInfo().BlockIds[beforeBlock] + ")",
      "apply simp"
    };
    int countCases = 0;
    foreach (Block succ in beforeOptimizations.GetSuccessorBlocks(beforeBlock))
    {
      if (isLoopHead(succ, beforeOptimizations, beforeOptBlockToLoops, beforeToAfterBlock) && Loops.Contains(succ))
      {
        countCases = countCases + 1;
      }
    }

    if (beforeOptimizations.GetSuccessorBlocks(beforeBlock).Count() > 1 && beforeOptimizations.GetSuccessorBlocks(beforeBlock).Count() - countCases > 1) 
    {
      proofMethods.Add("apply (intro conjI)");
    }
    foreach (Block succ in beforeOptimizations.GetSuccessorBlocks(beforeBlock))
    {
      if (Loops.Count == 0)
      {
        proofMethods.Add("apply (rule " + blockLemmaName(succ) + ")");
      }
      else if (isLoopHead(succ, beforeOptimizations, beforeOptBlockToLoops, beforeToAfterBlock) && Loops.Contains(succ))
      {
        
      }
      else
      {
        var loopHeadsSucc = new List<string>();
        foreach (Block loop in beforeOptBlockToLoops[succ])
        {
          loopHeadsSucc.Add("(" + beforeOptProgAccess.BlockInfo().BlockIds[loop] + "," + afterOptProgAccess.BlockInfo().BlockIds[beforeToAfterBlock[loop]] + ")");
        }
        proofMethods.Add("apply(rule exI[where ?x = \"{" + string.Join(",", loopHeadsSucc) + "}\"])");
        proofMethods.Add("apply simp");
        proofMethods.Add("apply (rule " +blockLemmaName(succ) + ")");
      }
      
    }
    proofMethods.Add("apply simp");
    if (beforeOptimizations.GetSuccessorBlocks(beforeBlock).Count() > 0)
    {
      proofMethods.Add("apply (unfold p_before_cfg_to_dag_prog.outEdges_" + afterOptProgAccess.BlockInfo().BlockIds[afterBlock] + ")");
    }
      
      
    if (beforeOptimizations.GetSuccessorBlocks(beforeBlock).Count() > 1)
    {
      proofMethods.Add("apply (intro conjI)");
    }
    foreach (Block succ in beforeOptimizations.GetSuccessorBlocks(beforeBlock))
    {
      proofMethods.Add("apply simp");
    }
    proofMethods.Add("apply (rule p_before_cfg_to_dag_prog.node_" + afterOptProgAccess.BlockInfo().BlockIds[afterBlock] + ")");
    proofMethods.Add("apply (rule p_unoptimized_cfg_prog.node_" + beforeOptProgAccess.BlockInfo().BlockIds[beforeBlock] + ")");
    proofMethods.Add("apply (unfold p_before_cfg_to_dag_prog.block_" + afterOptProgAccess.BlockInfo().BlockIds[afterBlock] + "_def p_unoptimized_cfg_prog.block_" +
                          beforeOptProgAccess.BlockInfo().BlockIds[beforeBlock]  + "_def)");
    proofMethods.Add("by simp");
    var varContextName = "\\<Lambda>";
    IList<Term> terms = new List<Term>();
    terms.Add(IsaCommonTerms.TermIdentFromName("A"));
    terms.Add(IsaCommonTerms.TermIdentFromName("M"));
    terms.Add(IsaCommonTerms.TermIdentFromName(varContextName));
    terms.Add(IsaCommonTerms.TermIdentFromName("\\<Gamma>"));
    terms.Add(IsaCommonTerms.TermIdentFromName("\\<Omega>"));
    terms.Add(IsaCommonTerms.TermIdentFromName("p_unoptimized_cfg_prog.proc_body"));
    terms.Add(IsaCommonTerms.TermIdentFromName("p_before_cfg_to_dag_prog.proc_body"));
    terms.Add(new NatConst(beforeOptProgAccess.BlockInfo().BlockIds[beforeBlock]));
    terms.Add(new NatConst(afterOptProgAccess.BlockInfo().BlockIds[afterBlock]));
    terms.Add(IsaCommonTerms.TermIdentFromName("{" + string.Join(",", loopHeads) + "}"));
    Term conclusion = new TermApp(IsaCommonTerms.TermIdentFromName("global_block_lemma_loop"), terms);
      
    var blockLemma = new LemmaDecl(
      blockLemmaName(beforeBlock), 
      conclusion,
      new Proof(proofMethods));
    return blockLemma;
  }
  public LemmaDecl HybridBlockLemmaTail( //show the hybrid block lemma for the tail of coalesced blocks
    Block beforeBlock,
    Block afterBlock,
    Func<Block, string> GlobalblockLemmaName,
    Func<Block, string> HybridblockLemmaName,
    IDictionary<Block, IList<Block>> beforeOptBlockToLoops,
    IList<Block> Loops)
  {
    var loopHeads = new List<string>();
    foreach (Block loop in Loops)
    {
      loopHeads.Add("(" + beforeOptProgAccess.BlockInfo().BlockIds[loop] + "," + afterOptProgAccess.BlockInfo().BlockIds[beforeToAfterBlock[loop]] + ")");
    }
    
    var function = new List<string>();
    foreach (Block succ in beforeOptimizations.GetSuccessorBlocks(beforeBlock))
    {
      if (beforeToAfterBlock.Keys.Contains(succ))
      {
        Block succAfter = beforeToAfterBlock[succ];
        function.Add("(" + beforeOptProgAccess.BlockInfo().BlockIds[succ] + "," + afterOptProgAccess.BlockInfo().BlockIds[succAfter] + ")");
      }
    }

    var proofMethods = new List<string>
    {

      "apply (rule loopBlock_global_block_hybrid[where ?f = \"the ∘ map_of [" + string.Join(",", function) + "]\"])",
      "apply (rule p_unoptimized_cfg_prog.outEdges_" + beforeOptProgAccess.BlockInfo().BlockIds[beforeBlock] + ")",
      "apply simp"
    };
    int countCases = 0;
    
    foreach (Block succ in beforeOptimizations.GetSuccessorBlocks(beforeBlock))
    {
      if (isLoopHead(succ, beforeOptimizations, beforeOptBlockToLoops, beforeToAfterBlock) && Loops.Contains(succ))
      {
        countCases++;
      }
    }

    if (beforeOptimizations.GetSuccessorBlocks(beforeBlock).Count() > 1 && beforeOptimizations.GetSuccessorBlocks(beforeBlock).Count() - countCases > 0) 
    {
      proofMethods.Add("apply (intro conjI)");
    }
    foreach (Block succ in beforeOptimizations.GetSuccessorBlocks(beforeBlock))
    {
      if (Loops.Count == 0)
      {
        proofMethods.Add("apply (rule " + GlobalblockLemmaName(succ) + ")");
      }
      else if (isLoopHead(succ, beforeOptimizations, beforeOptBlockToLoops, beforeToAfterBlock) && Loops.Contains(succ) && Loops.Contains(succ))
      {
        
      }
      else
      {
        var loopHeadsSucc = new List<string>();
        foreach (Block loop in beforeOptBlockToLoops[succ])
        {
          loopHeadsSucc.Add("(" + beforeOptProgAccess.BlockInfo().BlockIds[loop] + "," + afterOptProgAccess.BlockInfo().BlockIds[beforeToAfterBlock[loop]] + ")");
        }
        proofMethods.Add("apply(rule exI[where ?x = \"{" + string.Join(",", loopHeadsSucc) + "}\"])");
        proofMethods.Add("apply simp");
        proofMethods.Add("apply (rule " + GlobalblockLemmaName(succ) + ")");
      }
    }
    if (beforeOptimizations.GetSuccessorBlocks(beforeBlock).Count() > 0)
    {
      proofMethods.Add("apply simp");
      proofMethods.Add("apply (unfold p_before_cfg_to_dag_prog.outEdges_" +
                       afterOptProgAccess.BlockInfo().BlockIds[afterBlock] + ")");
    }
    
    proofMethods.Add("apply simp");
    proofMethods.Add("apply (unfold p_unoptimized_cfg_prog.node_" + beforeOptProgAccess.BlockInfo().BlockIds[beforeBlock] + " block_" + beforeOptProgAccess.BlockInfo().BlockIds[beforeBlock]+ "_def)");
    proofMethods.Add("by simp");
    
    var varContextName = "\\<Lambda>";
    IList<Term> terms = new List<Term>();
    terms.Add(IsaCommonTerms.TermIdentFromName("A"));
    terms.Add(IsaCommonTerms.TermIdentFromName("M"));
    terms.Add(IsaCommonTerms.TermIdentFromName(varContextName));
    terms.Add(IsaCommonTerms.TermIdentFromName("\\<Gamma>"));
    terms.Add(IsaCommonTerms.TermIdentFromName("\\<Omega>"));
    terms.Add(IsaCommonTerms.TermIdentFromName("p_unoptimized_cfg_prog.proc_body"));
    terms.Add(IsaCommonTerms.TermIdentFromName("p_before_cfg_to_dag_prog.proc_body"));
    terms.Add(new NatConst(beforeOptProgAccess.BlockInfo().BlockIds[beforeBlock]));
    terms.Add(new NatConst(afterOptProgAccess.BlockInfo().BlockIds[afterBlock]));
    terms.Add(IsaCommonTerms.TermIdentFromName("block_" + beforeOptProgAccess.BlockInfo().BlockIds[beforeBlock]));
    terms.Add(IsaCommonTerms.TermIdentFromName("{" + string.Join(",", loopHeads) + "}"));
    Term conclusion = new TermApp(IsaCommonTerms.TermIdentFromName("hybrid_block_lemma_loop"), terms);
    
    var blockLemma = new LemmaDecl(
      HybridblockLemmaName(beforeBlock), 
      conclusion,
      new Proof(proofMethods));
    return blockLemma;
  }

  public LemmaDecl HybridBlockLemma( //extend hybrid block lemma
    Block beforeBlock,
    Block afterBlock,
    Block succ,
    Func<Block, string> GlobalblockLemmaName,
    Func<Block, string> HybridblockLemmaName,
    IList<Block> Loops)
  {
    var proofMethods = new List<string>
    {
      "apply (rule extend_hybrid_global_block_lemma_loop)",
      "apply (rule " + HybridblockLemmaName(succ) + ")",
      "apply (rule p_unoptimized_cfg_prog.node_" + beforeOptProgAccess.BlockInfo().BlockIds[beforeBlock] +")",
      "apply (rule p_unoptimized_cfg_prog.outEdges_" + beforeOptProgAccess.BlockInfo().BlockIds[beforeBlock] + ")",
      "by simp"
    };
    
    var loopHeads = new List<string>();
    foreach (Block loop in Loops)
    {
      loopHeads.Add("(" + beforeOptProgAccess.BlockInfo().BlockIds[loop] + "," + afterOptProgAccess.BlockInfo().BlockIds[beforeToAfterBlock[loop]] + ")");
    }

    List<String> listCoalescedBlocks = new List<String>();
    Block curr = beforeBlock;
    listCoalescedBlocks.Add("block_" + beforeOptProgAccess.BlockInfo().BlockIds[curr]);
    while ((beforeOptimizations.GetSuccessorBlocks(curr).Count() == 1 &&
            beforeOptimizations.GetSuccessorBlocks(curr).First().Predecessors.Count() == 1))
    {
      curr = beforeOptimizations.GetSuccessorBlocks(curr).First();
      listCoalescedBlocks.Add("block_" + beforeOptProgAccess.BlockInfo().BlockIds[curr]);
      
    }
    
    var varContextName = "\\<Lambda>";
    IList<Term> terms = new List<Term>();
    terms.Add(IsaCommonTerms.TermIdentFromName("A"));
    terms.Add(IsaCommonTerms.TermIdentFromName("M"));
    terms.Add(IsaCommonTerms.TermIdentFromName(varContextName));
    terms.Add(IsaCommonTerms.TermIdentFromName("\\<Gamma>"));
    terms.Add(IsaCommonTerms.TermIdentFromName("\\<Omega>"));
    terms.Add(IsaCommonTerms.TermIdentFromName("p_unoptimized_cfg_prog.proc_body"));
    terms.Add(IsaCommonTerms.TermIdentFromName("p_before_cfg_to_dag_prog.proc_body"));
    terms.Add(new NatConst(beforeOptProgAccess.BlockInfo().BlockIds[beforeBlock]));
    terms.Add(new NatConst(afterOptProgAccess.BlockInfo().BlockIds[afterBlock]));
    terms.Add(IsaCommonTerms.TermIdentFromName("(" + string.Join("@", listCoalescedBlocks) + ")"));
    terms.Add(IsaCommonTerms.TermIdentFromName("{" + string.Join(",", loopHeads) + "}"));
    Term conclusion = new TermApp(IsaCommonTerms.TermIdentFromName("hybrid_block_lemma_loop"), terms);
    
    var blockLemma = new LemmaDecl(
      HybridblockLemmaName(beforeBlock), 
      conclusion,
      new Proof(proofMethods));
    return blockLemma;
  }

  public LemmaDecl ConvertHybridToGlobal( //show the hybrid block lemma for the head of coalesced blocks
    Block beforeBlock,
    Block afterBlock,
    Func<Block, string> GlobalblockLemmaName,
    Func<Block, string> HybridblockLemmaName,
    IList<Block> Loops)
  {
    var proofMethods = new List<string>
    {
      "apply (rule convert_hybrid_global_block_lemma_loop)",
      "apply (rule " + HybridblockLemmaName(beforeBlock) + ")"
    };
    
    List<String> listCoalescedBlocks = new List<String>();
    Block curr = beforeBlock;
    listCoalescedBlocks.Add("block_" + beforeOptProgAccess.BlockInfo().BlockIds[curr]);
    while ((beforeOptimizations.GetSuccessorBlocks(curr).Count() == 1 &&
            beforeOptimizations.GetSuccessorBlocks(curr).First().Predecessors.Count() == 1))
    {
      curr = beforeOptimizations.GetSuccessorBlocks(curr).First();
      listCoalescedBlocks.Add("block_" + beforeOptProgAccess.BlockInfo().BlockIds[curr]);
      
    }

    foreach (string b in listCoalescedBlocks)
    {
      proofMethods.Add("apply (unfold " + b + "_def)");
    }
    proofMethods.Add("apply (unfold p_before_cfg_to_dag_prog.node_" + afterOptProgAccess.BlockInfo().BlockIds[afterBlock] + " p_before_cfg_to_dag_prog.block_" + afterOptProgAccess.BlockInfo().BlockIds[afterBlock] + "_def)");
    proofMethods.Add("by simp");
    var loopHeads = new List<string>();
    foreach (Block loop in Loops)
    {
      loopHeads.Add("(" + beforeOptProgAccess.BlockInfo().BlockIds[loop] + "," + afterOptProgAccess.BlockInfo().BlockIds[beforeToAfterBlock[loop]] + ")");
    }
    var varContextName = "\\<Lambda>";
    IList<Term> terms = new List<Term>();
    terms.Add(IsaCommonTerms.TermIdentFromName("A"));
    terms.Add(IsaCommonTerms.TermIdentFromName("M"));
    terms.Add(IsaCommonTerms.TermIdentFromName(varContextName));
    terms.Add(IsaCommonTerms.TermIdentFromName("\\<Gamma>"));
    terms.Add(IsaCommonTerms.TermIdentFromName("\\<Omega>"));
    terms.Add(IsaCommonTerms.TermIdentFromName("p_unoptimized_cfg_prog.proc_body"));
    terms.Add(IsaCommonTerms.TermIdentFromName("p_before_cfg_to_dag_prog.proc_body"));
    terms.Add(new NatConst(beforeOptProgAccess.BlockInfo().BlockIds[beforeBlock]));
    terms.Add(new NatConst(afterOptProgAccess.BlockInfo().BlockIds[afterBlock]));
    terms.Add(IsaCommonTerms.TermIdentFromName("{" + string.Join(",", loopHeads) + "}"));
    Term conclusion = new TermApp(IsaCommonTerms.TermIdentFromName("global_block_lemma_loop"), terms);
    
    var blockLemma = new LemmaDecl(
      GlobalblockLemmaName(beforeBlock), 
      conclusion,
      new Proof(proofMethods));
    return blockLemma;
  }

  public LemmaDecl HybridBlockLemmaPruning( //Pruning of unreachable blocks with block coalescing
    Block beforeBlock,
    Block afterBlock,
    Func<Block, string> blockLemmaName,
    IList<Block> Loops)
  {
    var proofMethods = new List<string>
    {
      "apply (rule pruning_coalesced_loop)",
      "apply (rule p_before_cfg_to_dag_prog.node_" + afterOptProgAccess.BlockInfo().BlockIds[afterBlock] + ")",
      "apply (unfold p_unoptimized_cfg_prog.node_" + beforeOptProgAccess.BlockInfo().BlockIds[beforeBlock] + " p_unoptimized_cfg_prog.block_" + beforeOptProgAccess.BlockInfo().BlockIds[beforeBlock] + "_def)",
      "apply simp",
      "apply simp",
      "apply (unfold p_before_cfg_to_dag_prog.block_" + afterOptProgAccess.BlockInfo().BlockIds[afterBlock] + "_def)",
      "by simp"
    };
    var loopHeads = new List<string>();
    foreach (Block loop in Loops)
    {
      loopHeads.Add("(" + beforeOptProgAccess.BlockInfo().BlockIds[loop] + "," + afterOptProgAccess.BlockInfo().BlockIds[beforeToAfterBlock[loop]] + ")");
    }
    
    var varContextName = "\\<Lambda>";
    IList<Term> terms = new List<Term>();
    terms.Add(IsaCommonTerms.TermIdentFromName("A"));
    terms.Add(IsaCommonTerms.TermIdentFromName("M"));
    terms.Add(IsaCommonTerms.TermIdentFromName(varContextName));
    terms.Add(IsaCommonTerms.TermIdentFromName("\\<Gamma>"));
    terms.Add(IsaCommonTerms.TermIdentFromName("\\<Omega>"));
    terms.Add(IsaCommonTerms.TermIdentFromName("p_unoptimized_cfg_prog.proc_body"));
    terms.Add(IsaCommonTerms.TermIdentFromName("p_before_cfg_to_dag_prog.proc_body"));
    terms.Add(new NatConst(beforeOptProgAccess.BlockInfo().BlockIds[beforeBlock]));
    terms.Add(new NatConst(afterOptProgAccess.BlockInfo().BlockIds[afterBlock]));
    terms.Add(IsaCommonTerms.TermIdentFromName("block_" + beforeOptProgAccess.BlockInfo().BlockIds[beforeBlock]));
    terms.Add(IsaCommonTerms.TermIdentFromName("{" + string.Join(",", loopHeads) + "}"));
    Term conclusion = new TermApp(IsaCommonTerms.TermIdentFromName("hybrid_block_lemma_loop"), terms);
    
    var blockLemma = new LemmaDecl(
      blockLemmaName(beforeBlock), 
      conclusion,
      new Proof(proofMethods));
    return blockLemma;
  }

  public LemmaDecl LoopHeadNotCoalesced( //Loop Head uncoalesced
    Block beforeBlock,
    Block afterBlock,
    Func<Block, string> blockLemmaName,
    IDictionary<Block, IList<Block>> beforeOptBlockToLoops,
    IList<Block> Loops)
  {
    
    var loopHeads = new List<string>();
    foreach (Block loop in Loops)
    {
      loopHeads.Add("(" + beforeOptProgAccess.BlockInfo().BlockIds[loop] + "," + afterOptProgAccess.BlockInfo().BlockIds[beforeToAfterBlock[loop]] + ")");
    }
    
    var function = new List<string>();
    foreach (Block succ in beforeOptimizations.GetSuccessorBlocks(beforeBlock))
    {
      if (beforeToAfterBlock.Keys.Contains(succ))
      {
        Block succAfter = beforeToAfterBlock[succ];
        function.Add("(" + beforeOptProgAccess.BlockInfo().BlockIds[succ] + "," + afterOptProgAccess.BlockInfo().BlockIds[succAfter] + ")");
      }
    }
    var proofMethods = new List<string>
    {
      "apply (rule loopHead_global_block[where ?f = \"the ∘ map_of [" + string.Join(",", function) + "]\"])",
      "apply (rule p_unoptimized_cfg_prog.outEdges_" + beforeOptProgAccess.BlockInfo().BlockIds[beforeBlock] + ")",
      "apply simp"
    };
    
    int countCases = 0;
    
    foreach (Block succ in beforeOptimizations.GetSuccessorBlocks(beforeBlock))
    {
      if (isLoopHead(succ, beforeOptimizations, beforeOptBlockToLoops, beforeToAfterBlock) && Loops.Contains(succ))
      {
        countCases++;
      }
    }

    if (beforeOptimizations.GetSuccessorBlocks(beforeBlock).Count() > 1 && beforeOptimizations.GetSuccessorBlocks(beforeBlock).Count() - countCases > 0) 
    {
      proofMethods.Add("apply (intro conjI)");
    }
    foreach (Block succ in beforeOptimizations.GetSuccessorBlocks(beforeBlock))
    {
      if (isLoopHead(succ, beforeOptimizations, beforeOptBlockToLoops, beforeToAfterBlock) && Loops.Contains(succ))
      {
        
      }
      else
      {
        var loopHeadsSucc = new List<string>();
        foreach (Block loop in beforeOptBlockToLoops[succ])
        {
          loopHeadsSucc.Add("(" + beforeOptProgAccess.BlockInfo().BlockIds[loop] + "," + afterOptProgAccess.BlockInfo().BlockIds[beforeToAfterBlock[loop]] + ")");
        }
        proofMethods.Add("apply(rule exI[where ?x = \"{" + string.Join(",", loopHeadsSucc) + "}\"])");
        proofMethods.Add("apply simp");
        proofMethods.Add("apply (rule " + blockLemmaName(succ) + ")");
      }
      
    }
    proofMethods.Add("apply simp");
    if (beforeOptimizations.GetSuccessorBlocks(beforeBlock).Count() > 0)
    {
      proofMethods.Add("apply (unfold p_before_cfg_to_dag_prog.outEdges_" + afterOptProgAccess.BlockInfo().BlockIds[afterBlock] + ")");
    }
      
      
    if (beforeOptimizations.GetSuccessorBlocks(beforeBlock).Count() > 1)
    {
      proofMethods.Add("apply (intro conjI)");
    }
    foreach (Block succ in beforeOptimizations.GetSuccessorBlocks(beforeBlock))
    {
      proofMethods.Add("apply simp");
    }
    proofMethods.Add("apply (rule p_before_cfg_to_dag_prog.node_" + afterOptProgAccess.BlockInfo().BlockIds[afterBlock] + ")");
    proofMethods.Add("apply (rule p_unoptimized_cfg_prog.node_" + beforeOptProgAccess.BlockInfo().BlockIds[beforeBlock] + ")");
    proofMethods.Add("apply (unfold p_before_cfg_to_dag_prog.block_" + afterOptProgAccess.BlockInfo().BlockIds[afterBlock] + "_def p_unoptimized_cfg_prog.block_" +
                          beforeOptProgAccess.BlockInfo().BlockIds[beforeBlock]  + "_def)");
    proofMethods.Add("by simp");
    var varContextName = "\\<Lambda>";
    IList<Term> terms = new List<Term>();
    terms.Add(IsaCommonTerms.TermIdentFromName("A"));
    terms.Add(IsaCommonTerms.TermIdentFromName("M"));
    terms.Add(IsaCommonTerms.TermIdentFromName(varContextName));
    terms.Add(IsaCommonTerms.TermIdentFromName("\\<Gamma>"));
    terms.Add(IsaCommonTerms.TermIdentFromName("\\<Omega>"));
    terms.Add(IsaCommonTerms.TermIdentFromName("p_unoptimized_cfg_prog.proc_body"));
    terms.Add(IsaCommonTerms.TermIdentFromName("p_before_cfg_to_dag_prog.proc_body"));
    terms.Add(new NatConst(beforeOptProgAccess.BlockInfo().BlockIds[beforeBlock]));
    terms.Add(new NatConst(afterOptProgAccess.BlockInfo().BlockIds[afterBlock]));
    terms.Add(IsaCommonTerms.TermIdentFromName("{" + string.Join(",", loopHeads) + "}"));
    Term conclusion = new TermApp(IsaCommonTerms.TermIdentFromName("global_block_lemma_loop"), terms);
      
    var blockLemma = new LemmaDecl(
      blockLemmaName(beforeBlock), 
      conclusion,
      new Proof(proofMethods));
    return blockLemma;
  }

  public LemmaDecl LoopHeadCoalesced( //Loop Head coalesced
    Block beforeBlock,
    Block afterBlock,
    Func<Block, string> GlobalblockLemmaName,
    Func<Block, string> HybridblockLemmaName,
    IList<Block> Loops)
  {
    var loopHeads = new List<string>();
    foreach (Block loop in Loops)
    {
      loopHeads.Add("(" + beforeOptProgAccess.BlockInfo().BlockIds[loop] + "," + afterOptProgAccess.BlockInfo().BlockIds[beforeToAfterBlock[loop]] + ")");
    }

    
    
    var proofMethods = new List<string>
    {
      "apply (rule loopHead_global_block_hybrid)",
      "apply (rule p_unoptimized_cfg_prog.outEdges_" + beforeOptProgAccess.BlockInfo().BlockIds[beforeBlock] + ")",
      "apply simp",
      "apply (rule " + HybridblockLemmaName(beforeOptimizations.GetSuccessorBlocks(beforeBlock).FirstOrDefault()) + ")",
      "apply (rule p_unoptimized_cfg_prog.node_" + beforeOptProgAccess.BlockInfo().BlockIds[beforeBlock] + ")",
      "apply (rule p_before_cfg_to_dag_prog.node_" + afterOptProgAccess.BlockInfo().BlockIds[afterBlock] + " )",
      "apply (unfold p_before_cfg_to_dag_prog.block_" + afterOptProgAccess.BlockInfo().BlockIds[afterBlock] +"_def)",
      "apply (unfold p_unoptimized_cfg_prog.block_" + beforeOptProgAccess.BlockInfo().BlockIds[beforeBlock] +"_def)",
      "apply (unfold p_unoptimized_cfg_prog.block_" + beforeOptProgAccess.BlockInfo().BlockIds[beforeOptimizations.GetSuccessorBlocks(beforeBlock).FirstOrDefault()] +"_def)",
      "by simp"
    };
    
    List<String> listCoalescedBlocks = new List<String>();
    Block curr = beforeBlock;
    listCoalescedBlocks.Add("block_" + beforeOptProgAccess.BlockInfo().BlockIds[curr]);
    while ((beforeOptimizations.GetSuccessorBlocks(curr).Count() == 1 &&
            beforeOptimizations.GetSuccessorBlocks(curr).First().Predecessors.Count() == 1))
    {
      curr = beforeOptimizations.GetSuccessorBlocks(curr).First();
      listCoalescedBlocks.Add("block_" + beforeOptProgAccess.BlockInfo().BlockIds[curr]);
      
    }
    
    var varContextName = "\\<Lambda>";
    IList<Term> terms = new List<Term>();
    terms.Add(IsaCommonTerms.TermIdentFromName("A"));
    terms.Add(IsaCommonTerms.TermIdentFromName("M"));
    terms.Add(IsaCommonTerms.TermIdentFromName(varContextName));
    terms.Add(IsaCommonTerms.TermIdentFromName("\\<Gamma>"));
    terms.Add(IsaCommonTerms.TermIdentFromName("\\<Omega>"));
    terms.Add(IsaCommonTerms.TermIdentFromName("p_unoptimized_cfg_prog.proc_body"));
    terms.Add(IsaCommonTerms.TermIdentFromName("p_before_cfg_to_dag_prog.proc_body"));
    terms.Add(new NatConst(beforeOptProgAccess.BlockInfo().BlockIds[beforeBlock]));
    terms.Add(new NatConst(afterOptProgAccess.BlockInfo().BlockIds[afterBlock]));
    terms.Add(IsaCommonTerms.TermIdentFromName("{" + string.Join(",", loopHeads) + "}"));
    Term conclusion = new TermApp(IsaCommonTerms.TermIdentFromName("global_block_lemma_loop"), terms);
      
    var blockLemma = new LemmaDecl(
      GlobalblockLemmaName(beforeBlock), 
      conclusion,
      new Proof(proofMethods));
    return blockLemma;
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
  
}