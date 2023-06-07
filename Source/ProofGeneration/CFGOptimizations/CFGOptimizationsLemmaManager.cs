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
  public CFGOptimizationsLemmaManager(
    IProgramAccessor beforeDagProgAcces,
    IProgramAccessor afterCfgProgAccess,
    BoogieContextIsa boogieContext,
    CFGRepr beforeOptimizations,
    CFGRepr afterOptimizations,
    string funContextWfName,
    IDictionary<Block, Block> beforeToAfterBlock
  )
  {

  }

  public LemmaDecl GlobalBlockLemmaPruningNotCoalesced( //Pruning of unreachable blocks where no coalescing happened
    Block beforeBlock,
    Block afterBlock,
    string blockLemmaName)
  {
    var proofMethods = new List<string>
    {
      "apply (rule pruning_not_coalesced_loop)",
      "apply (rule p_unoptimized_cfg_prog.outEdges_" + beforeBlock.UniqueId + ")",
      "apply (rule p_before_cfg_to_dag_prog.node_" + afterBlock.UniqueId + ")",
      "apply (rule p_unoptimized_cfg_prog.node_" + beforeBlock.UniqueId + ")",
      "apply (unfold p_unoptimized_cfg_prog.block_" + beforeBlock.UniqueId + "_def)",
      "apply simp",
      "apply (unfold p_before_cfg_to_dag_prog.block_" + afterBlock.UniqueId + "_def)",
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
    terms.Add(new NatConst(beforeBlock.UniqueId));
    terms.Add(new NatConst(afterBlock.UniqueId));
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
    string blockLemmaName)
  {
    if (beforeBlock.succCount == 0)
    {
      var proofMethods = new List<string>
      {
        "apply (rule loopBlock_global_block)",
        "apply (rule p_unoptimized_cfg_prog.outEdges_" + beforeBlock.UniqueId + ")",
        "apply (auto)",
        "apply (unfold p_before_cfg_to_dag_prog.node_" + afterBlock.UniqueId + ")",
        "apply (unfold p_unoptimized_cfg_prog.node_" + beforeBlock.UniqueId + ")",
        "apply (unfold p_before_cfg_to_dag_prog.block_" + afterBlock.UniqueId + "_def p_unoptimized_cfg_prog.block_" +
        beforeBlock.UniqueId + "_def)",
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
      terms.Add(new NatConst(beforeBlock.UniqueId));
      terms.Add(new NatConst(afterBlock.UniqueId));
      terms.Add(IsaCommonTerms.EmptySet);
      Term conclusion = new TermApp(IsaCommonTerms.TermIdentFromName("global_block_lemma_loop"), terms);
      
      
      var blockLemma = new LemmaDecl(
        blockLemmaName, 
        conclusion,
        new Proof(proofMethods));
      return blockLemma;
    }
    else
    {
      var proofMethods = new List<string>
      {
        "apply (rule loopBlock_global_block[where ?f = \"how\" ]",
        "apply (rule p_unoptimized_cfg_prog.outEdges_" + beforeBlock.UniqueId + ")",
        "apply (unfold how_def)",
        "apply simp",
        "apply (intro conjI)"
      };
      //foreach (Block succ in beforeBlock.Predecessors) 
      var varContextName = "\\<Lambda>";
      IList<Term> terms = new List<Term>();
      terms.Add(IsaCommonTerms.TermIdentFromName("A"));
      terms.Add(IsaCommonTerms.TermIdentFromName("M"));
      terms.Add(IsaCommonTerms.TermIdentFromName(varContextName));
      terms.Add(IsaCommonTerms.TermIdentFromName("\\<Gamma>"));
      terms.Add(IsaCommonTerms.TermIdentFromName("\\<Omega>"));
      terms.Add(IsaCommonTerms.TermIdentFromName("p_unoptimized_cfg_prog.proc_body"));
      terms.Add(IsaCommonTerms.TermIdentFromName("p_before_cfg_to_dag_prog.proc_body"));
      terms.Add(new NatConst(beforeBlock.UniqueId));
      terms.Add(new NatConst(afterBlock.UniqueId));
      terms.Add(IsaCommonTerms.EmptySet);
      Term conclusion = new TermApp(IsaCommonTerms.TermIdentFromName("global_block_lemma_loop"), terms);
      
      var blockLemma = new LemmaDecl(
        blockLemmaName, 
        conclusion,
        new Proof(proofMethods));
      return blockLemma;
    }
  }


}