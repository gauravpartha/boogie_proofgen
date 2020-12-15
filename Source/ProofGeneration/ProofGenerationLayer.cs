using System;
using System.Collections;
using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;
using ProofGeneration.CFGRepresentation;
using ProofGeneration.Isa;
using ProofGeneration.IsaPrettyPrint;
using ProofGeneration.VCProofGen;
using ProofGeneration.ProgramToVCProof;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using Microsoft.Boogie.ProofGen;
using ProofGeneration.Util;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.BoogieIsaInterface.VariableTranslation;
using Microsoft.Boogie.TypeErasure;
using ProofGeneration.Passification;

namespace ProofGeneration
{
    public class ProofGenerationLayer
    {
        private static Implementation afterPassificationImpl;

        private static IDictionary<Block, Block> beforeDagOrigBlock;
        private static CFGRepr beforeDagCfg;

        private static BoogieMethodData beforeDagData;


        private static IDictionary<Block, Block> beforePassiveOrigBlock;
        private static CFGRepr beforePassificationCfg;

        private static BoogieMethodData beforePassiveData;

        private static CFGRepr afterPassificationCfg;
        private static CFGRepr noEmptyBlocksCfg;
        private static CFGRepr afterUnreachablePruningCfg;

        private static BoogieMethodData finalProgData;
        private static IVariableTranslationFactory varTranslationFactory;

        private static BoogieGlobalData boogieGlobalData;

        private static IDictionary<Block, IDictionary<Variable, Expr>> initialVarMapping = new Dictionary<Block, IDictionary<Variable, Expr>>();
        private static IDictionary<Variable, Variable> passiveToOrigVar = new Dictionary<Variable, Variable>();

        //VC Automation Hints
        private static VCHintManager vcHintManager;
        private static TypePremiseEraserFactory typePremiseEraserFactory;
        
        //Passification Automation Hints
        private static PassificationHintManager passificationHintManager; 

        public static void Program(Program p)
        {
            boogieGlobalData = new BoogieGlobalData(p.Functions, p.Axioms, p.GlobalVariables, p.Constants);
        }

        public static void BeforeCFGToDAG(Implementation impl)
        {
            beforeDagCfg = CFGReprTransformer.GetCfgRepresentation(impl, 
                true, 
                true, 
                out beforeDagOrigBlock, 
                out List<Variable> newVarsFromDesugaring, 
                false);
            beforeDagData = MethodDataFromImpl(impl, boogieGlobalData, newVarsFromDesugaring);
        }

        public static void BeforePassification(Implementation impl)
        {
            beforePassificationCfg = CFGReprTransformer.GetCfgRepresentation(
                impl, 
                true,
                true,
                out beforePassiveOrigBlock,
                out List<Variable> newVarsFromDesugaring
                );
            beforePassiveData = MethodDataFromImpl(impl, boogieGlobalData, newVarsFromDesugaring);
            passificationHintManager = new PassificationHintManager(beforePassiveOrigBlock);
        }

        private static BoogieMethodData MethodDataFromImpl(
            Implementation impl, 
            BoogieGlobalData globalData,
            List<Variable> extraLocalVariables = null
            )
        {
            //add out params to local variables for now
            var locals = new List<Variable>(impl.LocVars).Union(impl.OutParams);
            if (extraLocalVariables != null)
                locals = locals.Union(extraLocalVariables);
            
            return new BoogieMethodData(
                globalData,
                new List<TypeVariable>(impl.TypeParameters),
                new List<Variable>(impl.InParams),
                locals,
                null,
                new List<IdentifierExpr>(impl.Proc.Modifies),
                new List<Requires>(impl.Proc.Requires),
                new List<Ensures>(impl.Proc.Ensures));
        }

        public static void RecordInitialVariableMapping(Block b, IDictionary<Variable, Expr> variableToExpr)
        {
            Contract.Requires(b != null);
            Contract.Requires(variableToExpr != null);

            initialVarMapping.Add(b, new Dictionary<Variable, Expr>(variableToExpr));
        }

        public static void AfterPassificationCheckGlobalMap(Implementation impl)
        {
            finalProgData = MethodDataFromImpl(impl, boogieGlobalData);
            afterPassificationImpl = impl;
            afterPassificationCfg = CFGReprTransformer.getCFGRepresentation(impl);

            var passiveBlocks = new List<Block>(impl.Blocks);
            
            GlobalVersion globalVersion = new GlobalVersion();
            var globalVersionMap = globalVersion.GlobalVersionMap(
                beforePassificationCfg.entry.liveVarsBefore,
                afterPassificationCfg.entry, 
                passiveBlocks);
            
            Console.WriteLine("Version map: " + string.Join(Environment.NewLine, globalVersionMap));
            
            var versionMapCorrect = 
                GlobalVersionChecker.CheckVersionMap(globalVersionMap, 
                passificationHintManager, initialVarMapping,
                beforePassificationCfg, beforePassiveOrigBlock);

            if (!versionMapCorrect)
            {
                throw new ProofGenUnexpectedStateException(typeof(ProofGenerationLayer), "Incorrect version map");
            }
        }
        
        public static void AfterPassification(Implementation impl)
        {
            finalProgData = MethodDataFromImpl(impl, boogieGlobalData);
            afterPassificationImpl = impl;
            afterPassificationCfg = CFGReprTransformer.getCFGRepresentation(impl);

            var nameToVar = new Dictionary<string, Variable>();

            foreach(Variable v in beforePassiveData.InParams.Union(beforePassiveData.Locals))
            {
                nameToVar.Add(v.Name, v);
            }

            foreach(Variable vPassive in finalProgData.InParams.Union(finalProgData.Locals))
            {
                //heuristic to get mapping
                string [] split = vPassive.Name.Split('@');
                if(nameToVar.TryGetValue(split[0], out Variable vOrig))
                {
                    passiveToOrigVar.Add(vPassive, vOrig);
                } else
                {
                    //TODO
                    Console.Error.WriteLine("Cannot predict mapping between passive and original variable");
                    //throw new ProofGenUnexpectedStateException(typeof(ProofGenerationLayer), "Cannot predict mapping between passive and original variable");
                }
            } 
        }

        /*
        public static void AfterEmptyBlockRemoval(Implementation impl)
        {
            need to check predecessor issue
            //beforeDagCfg = CFGReprTransformer.GetCfgRepresentation(impl, true, out beforeDagOrigBlock, false);
            // noEmptyBlocksCfg = CFGReprTransformer.getCFGRepresentation(impl);
        }
        */

        public static void AfterUnreachablePruning(Implementation impl)
        {
            afterUnreachablePruningCfg = CFGReprTransformer.getCFGRepresentation(impl);
        }

        /// <summary> Records hint for a cmd in the final passified Boogie program</summary>
        /// <param name="cmd">command</param>
        /// <param name="block">block containing command</param>
        /// <param name="exprVC">the computed VC for the expression in the command</param>
        /// <param name="postVC">the computed postcondition of the command</param>
        /// <param name="resultVC">Wlp(cmd, postVC)</param>
        /// <param name="subsumptionOption">The subsumption option for this cmd.</param>
        public static void NextVcHintForBlock(
            Cmd cmd, 
            Block block, 
            VCExpr exprVC, 
            VCExpr postVC, 
            VCExpr resultVC, 
            CommandLineOptions.SubsumptionOption subsumptionOption
            )
        {
            vcHintManager.NextHintForBlock(cmd, block, exprVC, postVC, resultVC, subsumptionOption);
        }

        public static void NextPassificationHint(Block block, Cmd cmd, Variable origVar, Expr passiveExpr)
        {
           passificationHintManager.AddHint(block, cmd, origVar, passiveExpr); 
        }

        public static void SetTypeEraserFactory(TypePremiseEraserFactory factory)
        {
            typePremiseEraserFactory = factory;
            IsaUniqueNamer uniqueNamer = new IsaUniqueNamer();
            /* Hack: try to make sure unique namer uses names for Boogie functions that are different from the default name
             * otherwise it clashes with the functions potentially fixed in the context of a locale
             */
            foreach(var fun in boogieGlobalData.Functions)
            {
                uniqueNamer.GetName(fun.Name, "o_"+fun.Name);
            }

            var translator = new VCExprToIsaTranslator(uniqueNamer);
            translator.SetFunctionNamer(uniqueNamer);
            
            vcHintManager = new VCHintManager(factory, translator);
        }

        //axiom builder is null iff types are not erased (since no polymorphism in vc)
        public static void VCGenerateAllProofs(
            VCExpr vc, 
            VCExpr vcAxioms, 
            VCExpr typeAxioms,
            List<VCAxiomInfo> typeAxiomInfo,
            VCExpressionGenerator gen, 
            Boogie2VCExprTranslator translator,
            TypeAxiomBuilderPremisses axiomBuilder)
        {
            if(axiomBuilder == null && typeAxioms != null)
                throw new ArgumentException("type axioms can only be null if axiom builder is null");
            #region before passive program
            var fixedVarTranslation2 = new DeBruijnFixedVarTranslation(beforePassiveData);
            var fixedTyVarTranslation2 = new DeBruijnFixedTVarTranslation(beforePassiveData);
            var varTranslationFactory2 = new DeBruijnVarFactory(fixedVarTranslation2, fixedTyVarTranslation2, boogieGlobalData);

            Console.WriteLine("**Before passive prog mapping: " + fixedVarTranslation2.OutputMapping());
            
            string beforePassiveProgTheoryName = afterPassificationImpl.Name + "_before_passive_prog";
            var beforePassiveConfig = new IsaProgramGeneratorConfig(null, true,true, true, true);
            var beforePassiveProgAccess = new IsaProgramGenerator().GetIsaProgram(beforePassiveProgTheoryName, 
                afterPassificationImpl.Name, 
                beforePassiveData, beforePassiveConfig, varTranslationFactory2, 
                beforePassificationCfg, 
                out IList<OuterDecl> programDeclsBeforePassive,
                out IsaBlockInfo isaBlockInfoBeforePassive);
            #endregion
            
            
            
            List<VCExpr> vcBoogieAxioms = DeconstructAxiomsNoChecks(vcAxioms).ToList();
            int nAxioms = boogieGlobalData.Axioms.Count();

            List<VCExpr> consideredVCBoogieAxioms;
            
            if (axiomBuilder != null)
            {
                if(vcBoogieAxioms.Count != nAxioms + 3 )
                    //+3, since we currently ignore the three type ordering axioms
                    throw new ProofGenUnexpectedStateException(typeof(ProofGenerationLayer),
                    "vc axioms not in-sync with Boogie axioms");

                consideredVCBoogieAxioms = vcBoogieAxioms.GetRange(3, nAxioms);
            }
            else
            {
                if (nAxioms == 0)  
                {
                    if(vcBoogieAxioms.Count != 1 || !vcBoogieAxioms.First().Equals(VCExpressionGenerator.True))
                        throw new ProofGenUnexpectedStateException(typeof(ProofGenerationLayer),
                            "no axioms and no polymorphism, but vc axioms are not (syntactically) equivalent to True");

                    consideredVCBoogieAxioms = new List<VCExpr>();
                }
                else
                {
                    if (vcBoogieAxioms.Count != nAxioms)
                    {
                        throw new ProofGenUnexpectedStateException(typeof(ProofGenerationLayer),
                            "no axioms and no polymorphism, but vc axioms are not (syntactically) equivalent to True");
                    }

                    consideredVCBoogieAxioms = new List<VCExpr>(vcBoogieAxioms);
                }
            }


            //we get rid of the axioms that are "True"
            List<VCAxiomInfo> typeAxiomInfoPruned = new List<VCAxiomInfo>();
            List<VCExpr> vcTypeAxioms = new List<VCExpr>();
            if (axiomBuilder != null)
            {
                typeAxiomInfoPruned = typeAxiomInfo.Where(a => !a.Expr.Equals(VCExpressionGenerator.True)).ToList();
                vcTypeAxioms = DeconstructAxiomsNoChecks(typeAxioms).ToList();
                if (vcTypeAxioms.Count != typeAxiomInfoPruned.Count)
                {
                    throw new ProofGenUnexpectedStateException(typeof(ProofGenerationLayer),
                        "type axiom info not in-sync with actual type axioms");
                }
            }

            IEnumerable<VCExpr> vcAllAxioms =  consideredVCBoogieAxioms.Union(vcTypeAxioms);
            
            LocaleDecl vcLocale = VCToIsaInterface.ConvertVC(
                "vc",
                vc,
                vcAllAxioms,
                new StandardActiveDecl(),
                gen,
                translator,
                axiomBuilder,
                finalProgData,
                afterUnreachablePruningCfg,
                out VCInstantiation<Block> vcinst,
                out VCInstantiation<VCExpr> vcinstAxiom,
                out IVCVarFunTranslator vcTranslator,
                out IEnumerable<Function> vcFunctions);
            
            var lemmaNamer = new IsaUniqueNamer();

            var fixedVarTranslation = new DeBruijnFixedVarTranslation(finalProgData);
            var fixedTyVarTranslation = new DeBruijnFixedTVarTranslation(finalProgData);
            varTranslationFactory = new DeBruijnVarFactory(fixedVarTranslation, fixedTyVarTranslation, boogieGlobalData);

            string finalProgTheoryName = afterPassificationImpl.Name + "_passive_prog";
            var passiveProgConfig = new IsaProgramGeneratorConfig(beforePassiveProgAccess, false, false, false, false);
            var passiveProgAccess = new IsaProgramGenerator().GetIsaProgram(finalProgTheoryName, 
                afterPassificationImpl.Name, 
                finalProgData, passiveProgConfig, varTranslationFactory, 
                afterUnreachablePruningCfg, 
                out IList<OuterDecl> programDecls,
                out IsaBlockInfo blockInfo);
            
            StoreTheory(new Theory(finalProgTheoryName, new List<string> { "Boogie_Lang.Semantics", "Boogie_Lang.Util", beforePassiveProgAccess.TheoryName() }, programDecls));
            
            var passiveLemmaManager = new PassiveLemmaManager(vcinst, finalProgData, vcFunctions, blockInfo, vcTranslator, varTranslationFactory);
            IDictionary<Block, IList<OuterDecl>> finalProgramLemmas = GenerateVCLemmas(afterUnreachablePruningCfg, passiveLemmaManager, lemmaNamer);
            IDictionary<Block, OuterDecl> cfgProgramLemmas = GenerateCfgLemmas(afterUnreachablePruningCfg, finalProgramLemmas, passiveLemmaManager, passiveProgAccess.CfgDecl());
            //IDictionary<Block, LemmaDecl> beforePeepholeEmptyLemmas = GetAdjustedLemmas(afterPassificationCfg, afterUnreachablePruningCfg, passiveLemmaManager, lemmaNamer);

            //Contract.Assert(!finalProgramLemmas.Keys.Intersect(beforePeepholeEmptyLemmas.Keys).Any());
            
            List<OuterDecl> afterPassificationDecls = new List<OuterDecl>() { };
            foreach(var v in finalProgramLemmas.Values)
            {
                afterPassificationDecls.AddRange(v);
            }
            //fterPassificationDecls.AddRange(beforePeepholeEmptyLemmas.Values);
            afterPassificationDecls.AddRange(cfgProgramLemmas.Values);
            
            afterPassificationDecls.Add(passiveLemmaManager.MethodVerifiesLemma(
                afterUnreachablePruningCfg,
                passiveProgAccess.CfgDecl(),
                "method_verifies"));

            LocaleDecl afterPassificationLocale = GenerateLocale("passification", passiveLemmaManager, afterPassificationDecls);

            var passiveOuterDecls = new List<OuterDecl>() { vcLocale };
            passiveOuterDecls.Add(afterPassificationLocale);

            List<VCAxiomInfo> allAxiomsInfo = GetBoogieAxiomInfo(boogieGlobalData.Axioms, consideredVCBoogieAxioms);
            
            var vcBoogieInfo = new VcBoogieInfo(vcinst, vcinstAxiom, vcAllAxioms, allAxiomsInfo.Union(typeAxiomInfoPruned));

            var endToEnd = new EndToEndVCProof(
                finalProgData, 
                passiveProgAccess, 
                vcFunctions, 
                vcBoogieInfo,
                afterUnreachablePruningCfg, 
                varTranslationFactory,
                vcTranslator,
                typePremiseEraserFactory,
                gen);
            passiveOuterDecls.AddRange(endToEnd.GenerateProof());

            Theory theoryPassive = new Theory(afterPassificationImpl.Name+"_passive",
                new List<string> { "Boogie_Lang.Semantics", "Boogie_Lang.Util", "Boogie_Lang.VCHints", "Boogie_Lang.ExperimentalML", 
                    passiveProgAccess.TheoryName(), beforePassiveProgAccess.TheoryName() },
                passiveOuterDecls);

            StoreTheory(theoryPassive);
            
            #region before passive
            
            var passificationProgTheory = new Theory(beforePassiveProgTheoryName,
                new List<string> {"Boogie_Lang.Semantics", "Boogie_Lang.Util"}, programDeclsBeforePassive);
            StoreTheory(passificationProgTheory);
            
            Console.WriteLine("Passive prog mapping: " + fixedVarTranslation.OutputMapping());
            Console.WriteLine("Before passive prog mapping: " + fixedVarTranslation2.OutputMapping());

            var passificationProofDecls = new List<OuterDecl>();
            
            var beforePassiveLemmaManager = new PrePassiveLemmaManager(
                beforePassificationCfg,
                beforePassiveOrigBlock,
                isaBlockInfoBeforePassive,
                beforePassiveProgAccess,
                blockInfo,
                passiveProgAccess,
                passificationHintManager,
                initialVarMapping,
                beforePassiveData,
                varTranslationFactory2,
                varTranslationFactory
                );

            passificationProofDecls.AddRange(beforePassiveLemmaManager.Prelude());
            
            foreach (var block in beforePassificationCfg.GetBlocksBackwards())
            {
                Block origBlock = beforePassiveOrigBlock[block];
                if (afterUnreachablePruningCfg.ContainsBlock(origBlock))
                {
                    var lemma = beforePassiveLemmaManager.GenerateBlockLemma(block, 
                        beforePassificationCfg.GetSuccessorBlocks(block), GetLemmaName(block), null);
                    passificationProofDecls.Add(lemma);
                }
            }
            
            Theory passificationProofTheory = new Theory(afterPassificationImpl.Name+"_passification_proof",
                new List<string> { "Boogie_Lang.Semantics", "Boogie_Lang.Util", beforePassiveProgAccess.TheoryName(), passiveProgAccess.TheoryName(), "Boogie_Lang.Passification"},
                passificationProofDecls);
            StoreTheory(passificationProofTheory);
            #endregion
        }

        /// <summary>
        /// Get axiom information for those the user-defined axioms in the Boogie program.
        /// <paramref name="vcAxioms" /> may contain more than elements than <paramref name="axioms"/>, but the first
        /// n axioms should correspond to 
        /// </summary>
        private static List<VCAxiomInfo> GetBoogieAxiomInfo(IEnumerable<Axiom> axioms, List<VCExpr> vcAxioms)
        {
            var result = new List<VCAxiomInfo>();
            axioms.ZipDo(vcAxioms, (axiom, expr) =>
            {
               result.Add(new VcBoogieAxiomInfo(expr, axiom)); 
            });

            return result;
        }

        private static IEnumerable<VCExpr> DeconstructAxiomsNoChecks(VCExpr vcAxioms)
        {
            var result = new List<VCExpr>();
            VCExpr vcAxiomsTemp = vcAxioms;
            while (vcAxiomsTemp is VCExprNAry vcNAry && vcNAry.Op == VCExpressionGenerator.AndOp && vcNAry.Length == 2)
            {
                result.Add(vcNAry[1]);
                vcAxiomsTemp = vcNAry[0];
            }
            result.Add(vcAxiomsTemp);
            result.Reverse();
            return result;
        }

        private static IEnumerable<VCExpr> DeconstructAxioms(VCExpr vcAxioms)
        {
            int numAxioms = boogieGlobalData.Axioms.Count();

            /* Simplifying assumption: vcAxioms of the form (((Ax1 /\ Ax2) /\ Ax3) /\ Ax4) /\ ...
             * This is not true in general due to simplifications made by Boogie such as True /\ True -> True
             * Also, I don't know yet how type axioms are handled. */
            var result = new List<VCExpr>();

            if (numAxioms > 1)
            {
                VCExpr vcAxiomsTemp = vcAxioms;
                while (vcAxiomsTemp is VCExprNAry vcNAry && vcNAry.Op == VCExpressionGenerator.AndOp && vcNAry.Length == 2)
                {
                    result.Add(vcNAry[1]);
                    vcAxiomsTemp = vcNAry[0];
                }
                result.Add(vcAxiomsTemp);
                if (result.Count != numAxioms)
                {
                    throw new ProofGenUnexpectedStateException(typeof(ProofGenerationLayer),
                        "Not supported: vcAxioms not in -sync with Boogie axioms(could be due to optimizations / type axioms)");
                }
                result.Reverse();
                return result;
            } else if(numAxioms == 1 || (numAxioms == 0 && vcAxioms.Equals(VCExpressionGenerator.True)))
            {
                return new List<VCExpr> { vcAxioms };
            } else 
            {
                throw new ProofGenUnexpectedStateException(typeof(ProofGenUnexpectedStateException),
                    "Not supported: vcAxioms not in-sync with Boogie axioms (could be due to optimizations/type axioms)");
            }
        }

        private static ISet<Block> ComputeReachableEmptyBlocks(CFGRepr beforePeephole)
        {
            var result = new HashSet<Block>();

            Queue<Block> queue = new Queue<Block>();
            queue.Enqueue(beforePeephole.entry);

            while(queue.Any())
            {
                Block curBlock = queue.Dequeue();
                if(!LemmaHelper.FinalStateIsMagic(curBlock))
                {
                    if (curBlock.Cmds.Count == 0)
                        result.Add(curBlock);

                    foreach(Block bSucc in beforePeephole.GetSuccessorBlocks(curBlock))
                    {
                        queue.Enqueue(bSucc);
                    }
                }
            }

            return result;
        }

        private static IDictionary<Block, IList<OuterDecl>> GenerateVCLemmas(CFGRepr cfg, PassiveLemmaManager passiveLemmaManager, IsaUniqueNamer lemmaNamer)
        {
            var blockToLemmaDecls = new Dictionary<Block, IList<OuterDecl>>();

            foreach (Block b in cfg.GetBlocksBackwards())
            {
                //TODO move elsewhere
                var result = new List<OuterDecl>();
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
                result.Add(passiveLemmaManager.GenerateBlockLemma(b, cfg.GetSuccessorBlocks(b), lemmaNamer.GetName(b, GetLemmaName(b)), vcHintsName));
                blockToLemmaDecls.Add(b, result);
            }

            return blockToLemmaDecls;
        }
        private static IDictionary<Block, OuterDecl> GenerateCfgLemmas(CFGRepr cfg, IDictionary<Block, IList<OuterDecl>> lemmaDecls, PassiveLemmaManager passiveLemmaManager, Term cfgTerm)
        {
            var blockToLemmaDecls = new Dictionary<Block, OuterDecl>();

            foreach (Block b in cfg.GetBlocksBackwards())
            {
                //TODO move elsewhere
                var lemma = passiveLemmaManager.GenerateCfgLemma(b, cfg.GetSuccessorBlocks(b), cfgTerm, CfgLemmaName, (LemmaDecl) lemmaDecls[b].Last());
                blockToLemmaDecls.Add(b, lemma);
            }

            return blockToLemmaDecls;
        }
        private static string CfgLemmaName(Block b)
        {
            return "cfg_correct_" + b.Label;
        }

        //return first reachable blocks from block which are non-empty
        private static IEnumerable<Block> GetNonEmptySuccessors(Block block, CFGRepr cfg)
        {            
            //block is unreachable after peephole
            var nonEmptySuccessors = new List<Block>();

            if (cfg.NumOfSuccessors(block) > 0)
            {
                //find first reachable blocks that are not empty
                Queue<Block> toVisit = new Queue<Block>();
                toVisit.Enqueue(block);
                while (toVisit.Count > 0)
                {
                    Block curBlock = toVisit.Dequeue();

                    if (curBlock.Cmds.Count != 0)
                    {
                        nonEmptySuccessors.Add(curBlock);
                    }
                    else
                    {
                        foreach (Block succ in cfg.GetSuccessorBlocks(curBlock))
                        {
                            toVisit.Enqueue(succ);
                        }
                    }
                }
            }
                    
            return nonEmptySuccessors;
        }

        //assume that block identities in beforePruning and afterPruning are the same (only edges may be different)
        private static IDictionary<Block, LemmaDecl> GetAdjustedLemmas(CFGRepr beforePeepholeCfg, 
            CFGRepr afterPeepholeCfg, 
            IBlockLemmaManager lemmaManager, 
            IsaUniqueNamer lemmaNamer)
        {
            var blocksToLemmas = new Dictionary<Block, LemmaDecl>();

            foreach(Block block in beforePeepholeCfg.GetBlocksBackwards())
            {
                if(!afterPeepholeCfg.ContainsBlock(block))               
                {
                    //block is unreachable after peephole

                    if(block.Cmds.Count == 0)
                    {
                        var nonEmptySuccessors = GetNonEmptySuccessors(block, beforePeepholeCfg);

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

        /* old code
        private static IDictionary<Block, LemmaDecl> GenerateBeforePassiveLemmas(
            CFGRepr beforePassiveCfg,
            CFGRepr finalCfg,
            CFGRepr beforePeephole,
            PrePassiveLemmaManager prePassiveLemmaManager,
            IsaUniqueNamer lemmaNamer)
        {
            var blockToLemmaDecls = new Dictionary<Block, LemmaDecl>();

            ISet<Block> beforePeepholeReachable = ComputeReachableEmptyBlocks(beforePeephole);

            foreach (Block b in beforePassiveCfg.GetBlocksBackwards())
            {
                Block origBlock = beforePassiveOrigBlock[b];
                if (finalCfg.ContainsBlock(origBlock))
                {
                    LemmaDecl lemma = prePassiveLemmaManager.GenerateBlockLemma(
                        b,
                        finalCfg.GetSuccessorBlocks(origBlock),
                        lemmaNamer.GetName(b, GetLemmaName(b)),
                        null);
                    blockToLemmaDecls.Add(b, lemma);
                }
                else if (beforePeepholeReachable.Contains(origBlock))
                {
                    var nonEmptySuccessors = GetNonEmptySuccessors(origBlock, beforePeephole);
                    LemmaDecl lemma = prePassiveLemmaManager.GenerateEmptyBlockLemma(
                        b,
                        nonEmptySuccessors,
                        lemmaNamer.GetName(b, GetLemmaName(b)));
                    blockToLemmaDecls.Add(b, lemma);
                }
            }

            return blockToLemmaDecls;
        }

        private static IDictionary<Block, LemmaDecl> GetAdjustedPassiveLemmas(
            CFGRepr beforePassification,
            IDictionary<Block, Block> beforePassiveToOrig,
            CFGRepr beforePeephole,
            IBlockLemmaManager lemmaManager,
            IsaUniqueNamer lemmaNamer)
        {
            var blocksToLemmas = new Dictionary<Block, LemmaDecl>();

            foreach (Block block in beforePassification.GetBlocksBackwards())
            {
                Block origBlock = beforePassiveToOrig[block];

                if (origBlock.Cmds.Count == 0)
                {
                    var nonEmptySuccessors = GetNonEmptySuccessors(origBlock, beforePeephole);
                    blocksToLemmas.Add(block, lemmaManager.GenerateEmptyBlockLemma(block, nonEmptySuccessors, lemmaNamer.GetName(block, GetLemmaName(block))));
                }
            }

            return blocksToLemmas;
        }
        */

    }

}
