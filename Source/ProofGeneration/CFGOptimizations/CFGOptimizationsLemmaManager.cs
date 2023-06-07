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

  public LemmaDecl GlobalBlockLemmaPruning(
    Block beforeBlock,
    Block afterBlock,
    Func<Block, string> blockLemmaName,
    Func<Block, string> cfgLemmaName)
  {
    var proofMethods = new List<string>
    {
      "apply (rule pruning_not_coalesced_loop)",
      "apply (rule p_unoptimized_cfg_prog.outEdges_" + beforeBlock.UniqueId + ")",
      "apply (rule p_before_cfg_to_dag_prog.outEdges_" + afterBlock.UniqueId + ")",
      "apply (rule p_unoptimized_cfg_prog.node_" + beforeBlock.UniqueId + ")",
      "apply (unfold p_unoptimized_cfg_prog.block_" + beforeBlock.UniqueId + "_def)",
      "apply simp",
      "apply (unfold p_before_cfg_to_dag_prog.block_" + afterBlock.UniqueId + "_def)",
      "by simp"
    };
    
    //var blockLemma = new LemmaDecl(
    //  blockLemmaName(beforeBlock),
     // assumptions, //not sure what my assumptions should be
      //conclusion, //not sure what my conclusion should be
     // new Proof(proofMethods)
    //);
    return null;
  }


}