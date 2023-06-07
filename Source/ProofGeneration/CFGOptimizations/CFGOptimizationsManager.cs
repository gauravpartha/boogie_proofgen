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
    IProgramAccessor afterOptCfgProgAccess) //after CFG optimizations
    
  {
    
    var varContextName = "\\<Lambda>";
    var varContextAbbrev = new AbbreviationDecl(
      varContextName,
      new Tuple<IList<Term>, Term>(new List<Term>(), afterOptCfgProgAccess.VarContext()));
    
    var funContextWfName = "Wf_Fun";

    
    var BoogieContext = new BoogieContextIsa(
      IsaCommonTerms.TermIdentFromName("A"),
      IsaCommonTerms.TermIdentFromName("M"),
      IsaCommonTerms.TermIdentFromName(varContextName),
      IsaCommonTerms.TermIdentFromName("\\<Gamma>"),
      IsaCommonTerms.TermIdentFromName("\\<Omega>"));
    
    
    var lemmaManager = new CFGOptimizationsLemmaManager(
      afterOptCfgProgAccess,
      beforeOptCfgProgAcccess,
      BoogieContext,
      beforeOptimizations,
      afterOptimizations,
      funContextWfName,
      beforeToAfter); //TODO: Add necessary declarations

    var lemmaNamer = new IsaUniqueNamer();
    var outerDecls = new List<OuterDecl>();
    
    
    outerDecls.Add(varContextAbbrev);
    outerDecls.Add(new DeclareDecl("Nat.One_nat_def[simp del]"));
    List<string> proofMethods = new List<string>();
    
    //In a first try I assume that there is no block coalescing and no loops
    foreach (Block beforeBlock in beforeOptimizations.GetBlocksBackwards())
    {
      Block afterBlock = beforeToAfter[beforeBlock];
      if (ProgramToVCProof.LemmaHelper.FinalStateIsMagic(beforeBlock)) //If there is an assume or assert false statement in the block
      {
        var pruning = lemmaManager.GlobalBlockLemmaPruning(beforeBlock, afterBlock, null, null);
        outerDecls.Add(pruning);
      }
      else //otherwhise we just need to apply the normal global block lemma
      {
        if (beforeBlock.succCount == 0) //if the block has no successors
        {
          proofMethods.Add(ProofUtil.Apply("rule loopBlock_global_block"));
          proofMethods.Add(ProofUtil.Apply("rule p_unoptimized_cfg_prog.outEdges_" + beforeBlock.UniqueId));
          proofMethods.Add(ProofUtil.Apply("auto[1]"));
          proofMethods.Add(ProofUtil.Apply("auto[1]"));
          proofMethods.Add(ProofUtil.Apply("rule p_before_cfg_to_dag_prog.node_" + afterBlock.UniqueId));
          proofMethods.Add(ProofUtil.Apply("rule p_unoptimized_cfg_prog.node_" + beforeBlock.UniqueId));
          proofMethods.Add(ProofUtil.Apply("unfold p_before_cfg_to_dag_prog.block_" + afterBlock.UniqueId + "_def p_unoptimized_cfg_prog.block_" + beforeBlock.UniqueId + "_def"));
          proofMethods.Add(ProofUtil.Apply("simp"));
          proofMethods.Add("done");
          
        }
        else //Block was not coalesced and has successors. Assumption: Global Block Lemma holds for all successors
        {
          proofMethods.Add("");
        }
      }
    }

    List<string> importTheories = new List<string>
    {
      "Boogie_Lang.Ast", "Boogie_Lang.Ast_Cfg_Transformation", "Boogie_Lang.Semantics", "Boogie_Lang.Util", "CFGOptimizationsLoop",
      afterOptCfgProgAccess.TheoryName(),
      beforeOptCfgProgAcccess.TheoryName()
    };
    
    return new Theory(
      phasesTheories.TheoryName(PhasesTheories.Phase.CfgOptimizations), //TODO: Make sure that I did that correctly
      importTheories,
      outerDecls
    ); 
  }

  
}