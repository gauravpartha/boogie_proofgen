using System.Collections.Generic;
using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.BoogieIsaInterface.VariableTranslation;
using ProofGeneration.CFGRepresentation;
using ProofGeneration.Isa;

namespace ProofGeneration.Passification
{
    public class PassificationManager
    {
       public static Theory PassificationProof(
           string theoryName,
           CFGRepr beforePassificationCfg,
           CFGRepr finalCfg,
           IDictionary<Block, Block> origToPassiveBlock,
           IProgramAccessor beforePassiveProgAccess,
           IProgramAccessor passiveProgAccess,
           PassificationHintManager hintManager,
           IDictionary<Block, IDictionary<Variable,Expr>> initialVarMapping,
           BoogieMethodData beforePassiveData,
           IVariableTranslationFactory beforePassiveFactory,
           IVariableTranslationFactory passiveFactory)
       {
            
            var beforePassiveLemmaManager = new PrePassiveLemmaManager(
                beforePassificationCfg,
                origToPassiveBlock,
                beforePassiveProgAccess,
                passiveProgAccess,
                hintManager,
                initialVarMapping,
                beforePassiveData,
                beforePassiveFactory, 
                passiveFactory 
                );

            var passificationProofDecls = new List<OuterDecl>();
            passificationProofDecls.AddRange(beforePassiveLemmaManager.Prelude());
            
            foreach (var block in beforePassificationCfg.GetBlocksBackwards())
            {
                Block origBlock = origToPassiveBlock[block];
                if (true)
                {
                    var lemma = beforePassiveLemmaManager.GenerateBlockLemma(block, 
                        beforePassificationCfg.GetSuccessorBlocks(block), GetLemmaName(block), null);
                    passificationProofDecls.Add(lemma);
                }
            }
            
            return new Theory(theoryName,
                new List<string> { "Boogie_Lang.Semantics", "Boogie_Lang.Util", beforePassiveProgAccess.TheoryName(), passiveProgAccess.TheoryName(), "Boogie_Lang.Passification"},
                passificationProofDecls);
       }
       
       
       private static string GetLemmaName(Block b)
       {
           return "block_" + b.Label;
       }
    }
}