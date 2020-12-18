using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.BoogieIsaInterface.VariableTranslation;
using ProofGeneration.CFGRepresentation;
using ProofGeneration.Isa;
using ProofGeneration.Util;
using ProofGeneration.VCProofGen;

namespace ProofGeneration.ProgramToVCProof
{
    public class ProgramVcProofData
    {
        public IEnumerable<Function> VcFunctions { get; }
        public VcBoogieInfo VcBoogieInfo { get; }
        public VCHintManager VcHintManager { get;  }
        public LocaleDecl VcLocale { get; }
        public IVCVarFunTranslator VcTranslator { get; }
        
        public ProgramVcProofData(
            IEnumerable<Function> vcFunctions,
            VcBoogieInfo vcBoogieInfo,
            VCHintManager vcHintManager,
            LocaleDecl vcLocale,
            IVCVarFunTranslator vcTranslator)
        {
            VcFunctions = vcFunctions;
            VcBoogieInfo = vcBoogieInfo;
            VcHintManager = vcHintManager;
            VcLocale = vcLocale;
            VcTranslator = vcTranslator;
        }
    }
    /// <summary>
    /// Responsible for producing theory for the proof of the final Boogie program under the assumption of the VC
    /// </summary>
    public class ProgramToVcManager
    {
        
        public static Theory ProgramToVcProof(
            string theoryName,
            CFGRepr finalCfg,
            CFGRepr afterPassificationCfg,
            IProgramAccessor passiveProgAccess,
            IProgramAccessor beforePassiveProgAccess,
            BoogieMethodData methodData, 
            ProgramVcProofData vcProofData,
            IVariableTranslationFactory varFactory,
            TypePremiseEraserFactory eraserFactory,
            VCExpressionGenerator gen)
        {
            var lemmaNamer = new IsaUniqueNamer();
            var passiveLemmaManager = new PassiveLemmaManager(
                vcProofData.VcBoogieInfo.VcInst, 
                methodData, 
                vcProofData.VcFunctions, 
                passiveProgAccess.BlockInfo(), 
                vcProofData.VcTranslator, varFactory);

            var reachableBlocks = ReachableBlocks(afterPassificationCfg);
            
            IDictionary<Block, IList<OuterDecl>> finalProgramLemmas = 
                GenerateVCLemmas(afterPassificationCfg, finalCfg, reachableBlocks, passiveLemmaManager, vcProofData.VcHintManager, lemmaNamer);
            IDictionary<Block, OuterDecl> cfgProgramLemmas = 
                GenerateCfgLemmas(afterPassificationCfg, finalCfg, reachableBlocks, finalProgramLemmas, passiveLemmaManager, passiveProgAccess.CfgDecl(), lemmaNamer);

            
            List<OuterDecl> afterPassificationDecls = new List<OuterDecl>() { };
            foreach(var v in finalProgramLemmas.Values)
            {
                afterPassificationDecls.AddRange(v);
            }
            afterPassificationDecls.AddRange(cfgProgramLemmas.Values);
            
            afterPassificationDecls.Add(passiveLemmaManager.MethodVerifiesLemma(
                finalCfg,
                passiveProgAccess.CfgDecl(),
                "method_verifies"));

            LocaleDecl afterPassificationLocale = GenerateLocale("passification", passiveLemmaManager, afterPassificationDecls);

            var passiveOuterDecls = new List<OuterDecl>() { vcProofData.VcLocale };
            passiveOuterDecls.Add(afterPassificationLocale);

            var endToEnd = new EndToEndVCProof(
                methodData, 
                passiveProgAccess, 
                vcProofData.VcFunctions, 
                vcProofData.VcBoogieInfo,
                finalCfg, 
                varFactory,
                vcProofData.VcTranslator,
                eraserFactory,
                gen);
            passiveOuterDecls.AddRange(endToEnd.GenerateProof());

            return 
                new Theory(theoryName,
                new List<string> { "Boogie_Lang.Semantics", "Boogie_Lang.Util", "Boogie_Lang.VCHints", "Boogie_Lang.ExperimentalML", 
                    passiveProgAccess.TheoryName(), beforePassiveProgAccess.TheoryName() },
                passiveOuterDecls);
        }

        private static HashSet<Block> ReachableBlocks(CFGRepr cfg)
        {
            var reachableBlocks = new HashSet<Block>();
            Queue<Block> queue = new Queue<Block>();
            reachableBlocks.Add(cfg.entry);
            queue.Enqueue(cfg.entry);

            while (queue.TryDequeue(out Block b))
            {
                if (!LemmaHelper.FinalStateIsMagic(b))
                {
                    //b's successors are not trivially unreachable
                    var successors = cfg.GetSuccessorBlocks(b);
                    foreach (var suc in successors)
                    {
                        reachableBlocks.Add(suc);
                        queue.Enqueue(suc);
                    }
                }
            }

            return reachableBlocks;
        }
        
        
        //assume that block identities in beforePruning and afterPruning are the same (only edges may be different)
        private static IDictionary<Block, IList<OuterDecl>> GenerateVCLemmas(
            CFGRepr afterPassificationCfg,
            CFGRepr finalCfg, 
            HashSet<Block> reachableBlocks,
            PassiveLemmaManager passiveLemmaManager, 
            VCHintManager vcHintManager, 
            IsaUniqueNamer lemmaNamer)
        {
            var blockToLemmaDecls = new Dictionary<Block, IList<OuterDecl>>();

            foreach (Block b in afterPassificationCfg.GetBlocksBackwards())
            {
                var result = new List<OuterDecl>();
                
                if(finalCfg.ContainsBlock(b))               
                {
                    string vcHintsName = null;
                    if (vcHintManager.TryGetHints(b, out IEnumerable<VCHint> hints, out IEnumerable<OuterDecl> requiredDecls))
                    {
                        //FIXME potential val name clash
                        vcHintsName = b.Label + "_hints";
                        var code = MLUtil.DefineVal(b.Label + "_hints", MLUtil.MLList(hints));
                        //required declarations must be added first
                        result.AddRange(requiredDecls);
                        result.Add(new MLDecl(code));
                    }
                    result.Add(passiveLemmaManager.GenerateBlockLemma(b, finalCfg.GetSuccessorBlocks(b), lemmaNamer.GetName(b, GetLemmaName(b)), vcHintsName));
                    blockToLemmaDecls.Add(b, result);
                }
                else if(reachableBlocks.Contains(b))
                {
                    //block was removed after peephole but is reachable before peephole
                    if(b.Cmds.Count == 0)
                    {
                        //find the successors of b in the final cfg (i.e., the first non-empty reachable blocks)
                        var nonEmptyReachableSuccessors = GetNonEmptyReachableSuccessors(b, afterPassificationCfg, finalCfg); 
                        //add lemma
                        var decls = new List<OuterDecl>
                        {
                            passiveLemmaManager.GenerateEmptyBlockLemma(b, nonEmptyReachableSuccessors,
                                lemmaNamer.GetName(b, GetLemmaName(b)))
                        };
                        blockToLemmaDecls.Add(b, decls);
                    }
                    else
                    {
                        throw new ProofGenUnexpectedStateException("Non-empty reachable block removed during peep-hole");
                    }
                }
            }

            return blockToLemmaDecls;
        }
        private static IDictionary<Block, OuterDecl> GenerateCfgLemmas(
            CFGRepr afterPassificationCfg,
            CFGRepr finalCfg,
            HashSet<Block> reachableBlocks,
            IDictionary<Block, IList<OuterDecl>> lemmaDecls, 
            PassiveLemmaManager passiveLemmaManager, 
            Term cfgTerm,
            IsaUniqueNamer lemmaNamer)
        {
            var blockToLemmaDecls = new Dictionary<Block, OuterDecl>();

            foreach (Block b in afterPassificationCfg.GetBlocksBackwards())
            {
                IEnumerable<Block> finalCfgSuccessors;
                if (!finalCfg.ContainsBlock(b))
                {
                    if (reachableBlocks.Contains(b))
                    {
                        finalCfgSuccessors = GetNonEmptyReachableSuccessors(b, afterPassificationCfg, finalCfg);
                    }
                    else
                    {
                        continue;
                    }
                }
                else
                {
                    finalCfgSuccessors = finalCfg.GetSuccessorBlocks(b);
                }
                var lemma = passiveLemmaManager.GenerateCfgLemma(
                    b, 
                    finalCfg.ContainsBlock(b),
                    afterPassificationCfg.GetSuccessorBlocks(b), 
                    finalCfgSuccessors,
                    cfgTerm, 
                    b => "cfg_"+lemmaNamer.GetName(b, b.Label), 
                    (LemmaDecl) lemmaDecls[b].Last());
                blockToLemmaDecls.Add(b, lemma);
            }

            return blockToLemmaDecls;
        }
        
        private static string GetLemmaName(Block b)
        {
            return "block_" + b.Label;
        }

        private static LocaleDecl GenerateLocale(string localeName, IBlockLemmaManager lemmaManager, IList<OuterDecl> coreLemmas)
        {
            IList<OuterDecl> prelude = lemmaManager.Prelude();
            prelude.AddRange(coreLemmas);
            return new LocaleDecl(localeName, lemmaManager.Context(), prelude);
        }

        //return first reachable blocks from block in afterPassificationCfg, which are non-empty and contained in finalCfg
        private static IEnumerable<Block> GetNonEmptyReachableSuccessors(Block block, CFGRepr afterPassificationCfg, CFGRepr finalCfg)
        {            
            //block is unreachable after peephole
            var nonEmptySuccessors = new HashSet<Block>();

            if (afterPassificationCfg.NumOfSuccessors(block) > 0)
            {
                //find first reachable blocks that are not empty
                Queue<Block> toVisit = new Queue<Block>();
                toVisit.Enqueue(block);
                while (toVisit.Count > 0)
                {
                    Block curBlock = toVisit.Dequeue();

                    if (curBlock.Cmds.Count != 0 && finalCfg.ContainsBlock(curBlock))
                    {
                        nonEmptySuccessors.Add(curBlock);
                    }
                    else
                    {
                        foreach (Block succ in afterPassificationCfg.GetSuccessorBlocks(curBlock))
                        {
                            toVisit.Enqueue(succ);
                        }
                    }
                }
            }
                    
            return nonEmptySuccessors;
        }
    }
}