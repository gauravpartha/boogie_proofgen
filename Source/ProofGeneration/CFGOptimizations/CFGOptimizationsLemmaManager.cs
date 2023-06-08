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
  private readonly BoogieContextIsa boogieContext;
  private readonly CFGRepr beforeOptimizations;
  private readonly CFGRepr afterOptimizations;
  private readonly string funContextWfName;
  private readonly IDictionary<Block, Block> beforeToAfterBlock;
  public CFGOptimizationsLemmaManager(
    IProgramAccessor beforeOptProgAccess,
    IProgramAccessor afterOptProgAccess,
    BoogieContextIsa boogieContext,
    CFGRepr beforeOptimizations,
    CFGRepr afterOptimizations,
    string funContextWfName,
    IDictionary<Block, Block> beforeToAfterBlock
  )
  {
    this.beforeOptProgAccess = beforeOptProgAccess;
    this.afterOptProgAccess = afterOptProgAccess;
    this.boogieContext = boogieContext;
    this.beforeOptimizations = beforeOptimizations;
    this.afterOptimizations = afterOptimizations;
    this.funContextWfName = funContextWfName;
    this.beforeToAfterBlock = beforeToAfterBlock;
  }

  public LemmaDecl GlobalBlockLemmaPruningNotCoalesced( //Pruning of unreachable blocks where no coalescing happened
    Block beforeBlock,
    Block afterBlock,
    string blockLemmaName)
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
    terms.Add(IsaCommonTerms.EmptySet);
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
    Func<Block, string> blockLemmaName)
  {
    
    if (beforeOptimizations.GetSuccessorBlocks(beforeBlock).Count() == 0)
    {
      var proofMethods = new List<string>
      {
        "apply (rule loopBlock_global_block)",
        "apply (rule p_unoptimized_cfg_prog.outEdges_" + beforeOptProgAccess.BlockInfo().BlockIds[beforeBlock] + ")",
        "apply (auto)",
        "apply (unfold p_before_cfg_to_dag_prog.node_" + afterOptProgAccess.BlockInfo().BlockIds[afterBlock] + ")",
        "apply (unfold p_unoptimized_cfg_prog.node_" + beforeOptProgAccess.BlockInfo().BlockIds[beforeBlock] + ")",
        "apply (unfold p_before_cfg_to_dag_prog.block_" + afterOptProgAccess.BlockInfo().BlockIds[afterBlock] + "_def p_unoptimized_cfg_prog.block_" +
        beforeOptProgAccess.BlockInfo().BlockIds[beforeBlock]  + "_def)",
        "by simp"
      };

      
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
      terms.Add(IsaCommonTerms.EmptySet);
      Term conclusion = new TermApp(IsaCommonTerms.TermIdentFromName("global_block_lemma_loop"), terms);
      
      
      var blockLemma = new LemmaDecl(
        blockLemmaName(beforeBlock), 
        conclusion,
        new Proof(proofMethods));
      return blockLemma;
    }
    else
    {
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
        "apply simp",
        "apply (intro conjI)"
      };
      foreach (Block succ in beforeOptimizations.GetSuccessorBlocks(beforeBlock))
      {
        proofMethods.Add("apply (rule " + blockLemmaName(succ) + ")");
      }
      proofMethods.Add("apply simp");
      proofMethods.Add("apply (unfold p_before_cfg_to_dag_prog.outEdges_" + afterOptProgAccess.BlockInfo().BlockIds[afterBlock] + ")");
      proofMethods.Add("apply (intro conjI)");
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
      terms.Add(IsaCommonTerms.EmptySet);
      Term conclusion = new TermApp(IsaCommonTerms.TermIdentFromName("global_block_lemma_loop"), terms);
      
      var blockLemma = new LemmaDecl(
        blockLemmaName(beforeBlock), 
        conclusion,
        new Proof(proofMethods));
      return blockLemma;
    }
  }


}