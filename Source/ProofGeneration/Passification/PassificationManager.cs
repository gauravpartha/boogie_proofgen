using System.Collections.Generic;
using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.BoogieIsaInterface.VariableTranslation;
using ProofGeneration.CFGRepresentation;
using ProofGeneration.Isa;
using ProofGeneration.Util;

namespace ProofGeneration.Passification
{
    public class PassificationManager
    {
       public static Theory PassificationProof(
           string theoryName,
           CFGRepr beforePassificationCfg,
           IDictionary<Block, Block> nonPassiveToPassiveBlock,
           PassiveRelationGen relationGen,
           IProgramAccessor beforePassiveProgAccess,
           IProgramAccessor passiveProgAccess,
           BoogieMethodData beforePassiveData,
           IVariableTranslationFactory beforePassiveFactory,
           IVariableTranslationFactory passiveFactory)
       {
            
            var beforePassiveLemmaManager = new PrePassiveLemmaManager(
                beforePassificationCfg,
                nonPassiveToPassiveBlock,
                beforePassiveProgAccess,
                passiveProgAccess,
                relationGen,
                beforePassiveData,
                beforePassiveFactory, 
                passiveFactory 
                );
            
            var lemmaNamer = new IsaUniqueNamer();
            var passificationProofDecls = new List<OuterDecl>();
            passificationProofDecls.AddRange(beforePassiveLemmaManager.Prelude());

            var cfgLemmas = new List<OuterDecl>();
            
            foreach (var block in beforePassificationCfg.GetBlocksBackwards())
            {
                var localAndCfgLemma= 
                    beforePassiveLemmaManager.GenerateBlockLemma(
                        block, 
                        GetLemmaName(block, lemmaNamer),
                        b => GetCfgLemmaName(b, lemmaNamer));
                passificationProofDecls.Add(localAndCfgLemma.Item1);
                cfgLemmas.Add(localAndCfgLemma.Item2);
            }
            
            //add cfg lemmas at the end
            passificationProofDecls.AddRange(cfgLemmas);
            
            return new Theory(theoryName,
                new List<string> { "Boogie_Lang.Semantics", "Boogie_Lang.Util", beforePassiveProgAccess.TheoryName(), passiveProgAccess.TheoryName(), "Boogie_Lang.PassificationML"},
                passificationProofDecls);
       }
       
       
       private static string GetLemmaName(Block b, IsaUniqueNamer namer)
       {
           return namer.GetName(b, "block_" + b.Label);
       }

       private static string GetCfgLemmaName(Block b, IsaUniqueNamer namer)
       {
           return "cfg_"+namer.GetName(b, b.Label);
       }
    }
}