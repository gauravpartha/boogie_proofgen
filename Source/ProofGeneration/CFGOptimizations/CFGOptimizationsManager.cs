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
        var pruning = lemmaManager.GlobalBlockLemmaPruningNotCoalesced(beforeBlock, afterBlock, GetGlobalBlockLemmaName(beforeBlock, lemmaNamer));
        outerDecls.Add(pruning);
      }
      else //otherwhise we just need to apply the normal global block lemma. Assumption: Global Block Lemma holds for all successors
      {
        var globalBlock = lemmaManager.GlobalBlockLemma(beforeBlock, afterBlock, GetGlobalBlockLemmaName(beforeBlock, lemmaNamer));
        outerDecls.Add(globalBlock);
      }
    }

    List<string> importTheories = new List<string>
    {
      "Boogie_Lang.Ast", "Boogie_Lang.Ast_Cfg_Transformation", "Boogie_Lang.Semantics", "Boogie_Lang.Util", "Boogie_Lang.CFGOptimizationsLoop",
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

  
}