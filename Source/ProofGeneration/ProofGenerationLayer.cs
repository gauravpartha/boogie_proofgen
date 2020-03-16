
//#define PROOFGENACTIVE

using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;
using ProofGeneration.CFGRepresentation;
using ProofGeneration.Isa;
using ProofGeneration.IsaPrettyPrint;
using ProofGeneration.VCProofGen;
using ProofGeneration.ProgramToVCProof;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.IO;
using System;
using System.Linq;
using ProofGeneration.Util;

namespace ProofGeneration
{
    public class ProofGenerationLayer
    {
        private static Implementation afterPassificationImpl;

        private static IDictionary<Block, Block> beforePassiveOrigBlock;
        private static CFGRepr beforePassificationCfg;
        private static IEnumerable<Variable> beforePassiveInParams;
        private static IEnumerable<Variable> beforePassiveLocalVars;
        private static IEnumerable<Variable> beforePassiveOutParams;

        private static CFGRepr afterPassificationCfg;
        private static CFGRepr noEmptyBlocksCfg;
        private static CFGRepr afterUnreachablePruningCfg;

        private static IEnumerable<Function> functions;
        private static IEnumerable<Variable> inParams;
        private static IEnumerable<Variable> localVars;
        private static IEnumerable<Variable> outParams;

        private static IDictionary<Block, IDictionary<Variable, Variable>> finalVarMapping = new Dictionary<Block, IDictionary<Variable, Variable>>();
        private static IDictionary<Variable, Variable> passiveToOrigVar = new Dictionary<Variable, Variable>();


        [Conditional("PROOFGENACTIVE")]
        public static void StoreTheory(Implementation impl)
        {
            var programGenerator = new IsaProgramGenerator();
            var cfg = CFGReprTransformer.getCFGRepresentation(impl);
            Theory theory = programGenerator.GetIsaProgram(impl, cfg, impl.Proc.Name);

            StoreTheory(theory);
        }

        public static void Program(Program p)
        {
            functions = p.Functions;
        }

        public static void BeforePassification(Implementation impl)
        {
            beforePassificationCfg = CFGReprTransformer.getCFGRepresentation(impl, true, out beforePassiveOrigBlock);

            beforePassiveInParams = new List<Variable>(impl.InParams);
            beforePassiveLocalVars = new List<Variable>(impl.LocVars);
            beforePassiveOutParams = new List<Variable>(impl.OutParams);

            foreach (Variable v in impl.LocVars.Union(impl.InParams).Union(impl.OutParams))
            {
                passiveToOrigVar.Add(v, v);
            }
        }

        public static void RecordFinalVariableMapping(Block b, IDictionary<Variable, Expr> variableToExpr)
        {
            Contract.Requires(b != null);
            Contract.Requires(variableToExpr != null);

            var origVarToPassiveVar = new Dictionary<Variable, Variable>();

            foreach (var kv in variableToExpr)
            {
                if (kv.Value is IdentifierExpr ie && ie.Decl is Variable vPassive)
                {
                    origVarToPassiveVar.Add(kv.Key, vPassive);
                    if (passiveToOrigVar.TryGetValue(vPassive, out Variable origVarInMap))
                    {
                        if (origVarInMap != kv.Key)
                            throw new ProofGenUnexpectedStateException(typeof(ProofGenerationLayer), "passive variable corresponds to more than one original variables");
                    } else
                    {
                        passiveToOrigVar.Add(vPassive, kv.Key);
                    }
                }
            }

            finalVarMapping.Add(b, origVarToPassiveVar);
        }

        public static void AfterPassification(Implementation impl)
        {
            inParams = impl.InParams;
            localVars = impl.LocVars;
            outParams = impl.OutParams;
            afterPassificationImpl = impl;
            afterPassificationCfg = CFGReprTransformer.getCFGRepresentation(impl);
        }

        public static void AfterEmptyBlockRemoval(Implementation impl)
        {
            noEmptyBlocksCfg = CFGReprTransformer.getCFGRepresentation(impl);
        }

        public static void AfterUnreachablePruning(Implementation impl)
        {
            afterUnreachablePruningCfg = CFGReprTransformer.getCFGRepresentation(impl);
        }

        public static void VCGenerateAllProofs(VCExpr vc, VCExpressionGenerator gen, Boogie2VCExprTranslator translator)
        {
            LocaleDecl vcLocale = VCToIsaInterface.ConvertVC(
                "vc",
                vc,
                new StandardActiveDecl(),
                gen,
                translator,
                functions,
                inParams,
                localVars,
                afterUnreachablePruningCfg,
                out VCInstantiation vcinst);

            LocaleDecl vcPassiveLocale = VCToIsaInterface.ConvertVC(
                "vc_passive",
                vc,
                new PassiveActiveDecl(),
                gen,
                translator,
                functions,
                inParams,
                localVars,
                afterUnreachablePruningCfg,
                out VCInstantiation vcPassiveInst);

            var lemmaNamer = new IsaUniqueNamer();

            var passiveLemmaManager = new PassiveLemmaManager(vcinst, functions, inParams, localVars, outParams);
            IDictionary<Block, LemmaDecl> finalProgramLemmas = GenerateVCLemmas(afterUnreachablePruningCfg, passiveLemmaManager, lemmaNamer);
            IDictionary<Block, LemmaDecl> beforePeepholeEmptyLemmas = GetAdjustedLemmas(afterPassificationCfg, afterUnreachablePruningCfg, passiveLemmaManager, lemmaNamer);

            Contract.Assert(!finalProgramLemmas.Keys.Intersect(beforePeepholeEmptyLemmas.Keys).Any());

            List<OuterDecl> afterPassificationDecls = new List<OuterDecl>() { };
            afterPassificationDecls.AddRange(finalProgramLemmas.Values);
            afterPassificationDecls.AddRange(beforePeepholeEmptyLemmas.Values);

            LocaleDecl afterPassificationLocale = GenerateLocale("passification", passiveLemmaManager, afterPassificationDecls);


            #region WIP

            // Generate before passification block lemmas to try out things
            var beforePassiveNamer = new IsaUniqueNamer();

            var prePassiveLemmaManager = new PrePassiveLemmaManager(
                vcPassiveInst,
                beforePassiveOrigBlock,
                passiveToOrigVar,
                functions,
                beforePassiveLocalVars,
                beforePassiveInParams,
                beforePassiveOutParams
                );

            IDictionary<Block, LemmaDecl> beforePassiveLemmas =
                GenerateBeforePassiveLemmas(beforePassificationCfg, afterUnreachablePruningCfg, beforePeepholeEmptyLemmas, prePassiveLemmaManager, beforePassiveNamer);

            List<OuterDecl> beforePassiveDecls = new List<OuterDecl>();
            beforePassiveDecls.AddRange(beforePassiveLemmas.Values);

            LocaleDecl beforePassiveLocale = GenerateLocale("beforePassive", prePassiveLemmaManager, beforePassiveDecls);
            #endregion

            Theory theory = new Theory(afterPassificationImpl.Name,
                new List<string>() { "Semantics", "Util" },
                new List<OuterDecl>() { vcLocale, vcPassiveLocale, beforePassiveLocale });

            StoreTheory(theory);
        }

        private static IDictionary<Block, LemmaDecl> GenerateBeforePassiveLemmas(CFGRepr beforePassiveCfg,
            CFGRepr finalCfg,
            IDictionary<Block, LemmaDecl> emptyBlockLemmas,
            PrePassiveLemmaManager prePassiveLemmaManager, IsaUniqueNamer lemmaNamer)
        {
            var blockToLemmaDecls = new Dictionary<Block, LemmaDecl>();

            foreach (Block b in beforePassiveCfg.GetBlocksBackwards())
            {
                Block origBlock = beforePassiveOrigBlock[b];
                if (finalCfg.ContainsBlock(origBlock))
                {
                    LemmaDecl lemma = prePassiveLemmaManager.GenerateBlockLemma(
                        b,
                        finalCfg.GetSuccessorBlocks(origBlock),
                        lemmaNamer.GetName(b, GetLemmaName(b)));
                    blockToLemmaDecls.Add(b, lemma);
                }

                if (emptyBlockLemmas.TryGetValue(b, out LemmaDecl emptyBlockLemma))
                {
                    blockToLemmaDecls.Add(b, emptyBlockLemma);
                }
            }

            return blockToLemmaDecls;
        }

        private static IDictionary<Block, LemmaDecl> GenerateVCLemmas(CFGRepr cfg, PassiveLemmaManager passiveLemmaManager, IsaUniqueNamer lemmaNamer)
        {
            var blockToLemmaDecls = new Dictionary<Block, LemmaDecl>();

            foreach (Block b in cfg.GetBlocksBackwards())
            {
                blockToLemmaDecls.Add(b, passiveLemmaManager.GenerateBlockLemma(b, cfg.GetSuccessorBlocks(b), lemmaNamer.GetName(b, GetLemmaName(b))));
            }

            return blockToLemmaDecls;
        }

        //assume that block identities in beforePruning and afterPruning are the same (only edges may be different)
        private static IDictionary<Block, LemmaDecl> GetAdjustedLemmas(CFGRepr beforePeepholeCfg, 
            CFGRepr afterPeepholeCfg, 
            IBlockLemmaManager lemmaManager, 
            IsaUniqueNamer lemmaNamer)
        {
            var blocksToLemmas = new Dictionary<Block, LemmaDecl>();
            //TODO locale with state assumptions, adjustment of proofs etc...

            foreach(Block block in beforePeepholeCfg.GetBlocksBackwards())
            {
                if(!afterPeepholeCfg.ContainsBlock(block))               
                {
                    //block is unreachable after peephole

                    if(block.Cmds.Count == 0)
                    {
                        ISet<Block> nonEmptySuccessors = new HashSet<Block>();

                        if (beforePeepholeCfg.NumOfSuccessors(block) > 0)
                        {
                            //find first reachable blocks that are not empty
                            Queue<Block> toVisit = new Queue<Block>();
                            toVisit.Enqueue(block);
                            while (toVisit.Count > 0)
                            {
                                Block curBlock = toVisit.Dequeue();

                                if (curBlock.Cmds.Count != 0 || beforePeepholeCfg.NumOfSuccessors(curBlock) == 0)
                                {
                                    nonEmptySuccessors.Add(curBlock);
                                }
                                else
                                {
                                    foreach (Block succ in beforePeepholeCfg.GetSuccessorBlocks(curBlock))
                                    {
                                        toVisit.Enqueue(succ);
                                    }
                                }
                            }
                        } else
                        {
                            //empty exit block is removed, hence no assumptions required
                        }

                        //add lemma
                        blocksToLemmas.Add(block, lemmaManager.GenerateEmptyBlockLemma(block, nonEmptySuccessors, lemmaNamer.GetName(block, GetLemmaName(block))));
                    }
                }     
            }

            return blocksToLemmas;
        }

        private static LocaleDecl GenerateLocale(string localeName, IBlockLemmaManager lemmaManager, IList<OuterDecl> coreLemmas)
        {
            IList<OuterDecl> prelude = lemmaManager.Prelude();
            prelude.AddRange(coreLemmas);
            return new LocaleDecl(localeName, lemmaManager.Context(), prelude);
        }

        private static string GetLemmaName(Block b)
        {
            return "block_" + b.Label;
        }
        
        private static void StoreTheory(Theory theory)
        {
            var sw = new StreamWriter(theory.theoryName + ".thy");

            string theoryString = IsaPrettyPrinter.PrintTheory(theory);

            sw.WriteLine(theoryString);
            sw.Close();
        }

    }

}
