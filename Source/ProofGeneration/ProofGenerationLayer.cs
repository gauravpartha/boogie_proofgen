
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

        private static CFGRepr afterPassificationCfg;
        private static CFGRepr noEmptyBlocksCfg;
        private static CFGRepr afterUnreachablePruningCfg;

        private static IEnumerable<Function> functions;       
        private static IEnumerable<Variable> inParams;
        private static IEnumerable<Variable> localVars;

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
        }

        public static void AfterPassification(Implementation impl)
        {
            inParams = impl.InParams;
            localVars = impl.LocVars;
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
                vc, 
                gen, 
                translator, 
                functions, 
                inParams,
                localVars,
                afterUnreachablePruningCfg,
                out VCInstantiation vcinst);

            var lemmaNamer = new IsaUniqueNamer();

            var programToVCManager = new PassifiedProgToVCManager(vcinst, functions, inParams, localVars);
            IDictionary<Block, LemmaDecl> finalProgramLemmas = GenerateVCLemmas(afterUnreachablePruningCfg, programToVCManager, lemmaNamer);
            IDictionary<Block, LemmaDecl> beforePeepholeEmptyLemmas = GetAdjustedLemmas(afterPassificationCfg, afterUnreachablePruningCfg, programToVCManager, lemmaNamer);

            Contract.Assert(!finalProgramLemmas.Keys.Intersect(beforePeepholeEmptyLemmas.Keys).Any());

            IList<Tuple<TermIdent, TypeIsa>> fixedVariables = programToVCManager.GetFixedVariables();
            IList<Term> stateAssumptions = programToVCManager.GetStateAssumptions();
            IList<string> stateAssumptionLabels = stateAssumptions.Select((_, i) => "S" + i).ToList();
            var stateAssmsLemmas = new LemmasDecl("state_assms", stateAssumptionLabels);

            List<OuterDecl> afterPassificationDecls = new List<OuterDecl>() { stateAssmsLemmas };
            afterPassificationDecls.AddRange(finalProgramLemmas.Values);
            afterPassificationDecls.AddRange(beforePeepholeEmptyLemmas.Values);


            LocaleDecl afterPassificationLocale = new LocaleDecl("passification",
                new ContextElem(fixedVariables, stateAssumptions, stateAssumptionLabels),
                afterPassificationDecls);

            #region WIP

            // Generate before passification block lemmas to try out things
            var beforePassiveNamer = new IsaUniqueNamer();            

            IDictionary<Block, LemmaDecl> beforePassiveLemmas = 
                GenerateBeforePassiveLemmas(beforePassificationCfg, afterUnreachablePruningCfg, beforePeepholeEmptyLemmas, programToVCManager, beforePassiveNamer);

            List<OuterDecl> beforePassiveDecls = new List<OuterDecl>() { stateAssmsLemmas };
            beforePassiveDecls.AddRange(beforePassiveLemmas.Values);

            LocaleDecl beforePassiveLocale = new LocaleDecl("beforePassive",
               new ContextElem(fixedVariables, stateAssumptions, stateAssumptionLabels),
               beforePassiveDecls);

            #endregion


            Theory theory = new Theory(afterPassificationImpl.Name,
                new List<string>() { "Semantics", "Util" },
                new List<OuterDecl>() { vcLocale, beforePassiveLocale });

            StoreTheory(theory);
        }

        private static IDictionary<Block, LemmaDecl> GenerateBeforePassiveLemmas(CFGRepr beforePassiveCfg,
            CFGRepr finalCfg,
            IDictionary<Block, LemmaDecl> emptyBlockLemmas,
            PassifiedProgToVCManager progToVCManager, IsaUniqueNamer lemmaNamer)
        {
            var blockToLemmaDecls = new Dictionary<Block, LemmaDecl>();

            foreach (Block b in beforePassiveCfg.GetBlocksBackwards())
            {
                Block origBlock = beforePassiveOrigBlock[b];
                if (finalCfg.ContainsBlock(origBlock))
                {
                    LemmaDecl lemma = progToVCManager.GenerateVCPassiveBlockLemma(
                        b,
                        origBlock,
                        finalCfg.GetSuccessorBlocks(origBlock),
                        lemmaNamer.GetName(b, GetLemmaName(b)));
                    blockToLemmaDecls.Add(b, lemma);
                }

                if(emptyBlockLemmas.TryGetValue(b, out LemmaDecl emptyBlockLemma))
                {
                    blockToLemmaDecls.Add(b, emptyBlockLemma);
                }
            }

            return blockToLemmaDecls;
        }

            private static IDictionary<Block, LemmaDecl> GenerateVCLemmas(CFGRepr cfg, PassifiedProgToVCManager progToVCManager, IsaUniqueNamer lemmaNamer)
        {
            var blockToLemmaDecls = new Dictionary<Block, LemmaDecl>();

            foreach (Block b in cfg.GetBlocksBackwards())
            {
                blockToLemmaDecls.Add(b, progToVCManager.GenerateVCBlockLemma(b, cfg.GetSuccessorBlocks(b), lemmaNamer.GetName(b, GetLemmaName(b))));
            }

            return blockToLemmaDecls;
        }        

        //assume that block identities in beforePruning and afterPruning are the same (only edges may be different)
        private static IDictionary<Block, LemmaDecl> GetAdjustedLemmas(CFGRepr beforePeepholeCfg, 
            CFGRepr afterPeepholeCfg, 
            PassifiedProgToVCManager progToVCManager, 
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
                        blocksToLemmas.Add(block, progToVCManager.GenerateEmptyBlockLemma(block, nonEmptySuccessors, lemmaNamer.GetName(block, GetLemmaName(block))));
                    }
                }        
            }

            return blocksToLemmas;
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
