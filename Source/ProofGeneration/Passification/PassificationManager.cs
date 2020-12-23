using System;
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
           string boogieToVcTheoryName,
           LemmaDecl boogieToVcLemma,
           Term vcAssm,
           CFGRepr beforePassificationCfg,
           IDictionary<Block, Block> nonPassiveToPassiveBlock,
           PassiveRelationGen relationGen,
           IProgramAccessor beforePassiveProgAccess,
           IProgramAccessor passiveProgAccess,
           BoogieMethodData beforePassiveData,
           IVariableTranslationFactory beforePassiveFactory,
           IVariableTranslationFactory passiveFactory)
       {
            string varContextName = "\\<Lambda>1";
            string passiveVarContextName = "\\<Lambda>2";
            var varContextNonPassivePassive = Tuple.Create(varContextName, passiveVarContextName);
            
            var beforePassiveLemmaManager = new PrePassiveLemmaManager(
                beforePassificationCfg,
                nonPassiveToPassiveBlock,
                beforePassiveProgAccess,
                passiveProgAccess,
                varContextNonPassivePassive,
                relationGen,
                beforePassiveFactory, 
                passiveFactory 
                );
            
            var lemmaNamer = new IsaUniqueNamer();
            var passificationProofDecls = new List<OuterDecl>();
            
            var varContextAbbrev = new AbbreviationDecl(
                varContextName,
                new Tuple<IList<Term>, Term>(new List<Term>(), beforePassiveProgAccess.VarContext())
                );
            
            var passiveVarContextAbbrev = new AbbreviationDecl(
                passiveVarContextName,
                new Tuple<IList<Term>, Term>(new List<Term>(), passiveProgAccess.VarContext())
                );
            
            passificationProofDecls.Add(varContextAbbrev);
            passificationProofDecls.Add(passiveVarContextAbbrev);
            
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
            
            var endToEnd = new PassificationEndToEnd();

            passificationProofDecls.AddRange(endToEnd.EndToEndProof(
                GetCfgLemmaName(beforePassificationCfg.entry, lemmaNamer),
                boogieToVcTheoryName+"."+boogieToVcLemma.name,
                vcAssm,
                beforePassiveProgAccess,
                passiveProgAccess,
                varContextNonPassivePassive,
                beforePassificationCfg,
                relationGen.LiveVarsBeforeBlock(beforePassificationCfg.entry),
                passiveFactory.CreateTranslation().VarTranslation
            ));
            
            return new Theory(theoryName,
                new List<string> { "Boogie_Lang.Semantics", "Boogie_Lang.Util", beforePassiveProgAccess.TheoryName(), 
                    passiveProgAccess.TheoryName(), "Boogie_Lang.PassificationEndToEnd", "Boogie_Lang.PassificationML", boogieToVcTheoryName},
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