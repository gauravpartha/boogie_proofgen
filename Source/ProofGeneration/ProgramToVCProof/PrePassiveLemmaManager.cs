﻿using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.BoogieIsaInterface.VariableTranslation;
using ProofGeneration.CFGRepresentation;
using ProofGeneration.Isa;
using ProofGeneration.Util;

namespace ProofGeneration.ProgramToVCProof
{
    class PrePassiveLemmaManager : IBlockLemmaManager
    {
        private readonly CFGRepr cfg;
        private readonly IDictionary<Block, Block> origToPassiveBlock;
        private readonly IDictionary<Block, Block> passiveToOrigBlock;

        private readonly IDictionary<Variable, Variable> passiveToOrigVar;
        private readonly IDictionary<Block, IDictionary<Variable, Expr>> constantEntry;
        private readonly IDictionary<Block, IDictionary<Variable, Expr>> constantExit;

        private readonly BoogieMethodData methodData;
        private readonly IEnumerable<Variable> programVariables;

        private readonly BoogieContextIsa boogieContext;

        private readonly TermIdent normalInitState = IsaCommonTerms.TermIdentFromName("n_s");
        private readonly Term initState;
        private readonly TermIdent finalState = IsaCommonTerms.TermIdentFromName("s'");

        private readonly IDictionary<Function, TermIdent> funToInterpMapping;

        private readonly MultiCmdIsaVisitor cmdIsaVisitor;

        private readonly IVariableTranslationFactory varTranslationFactory;

        private readonly IsaUniqueNamer uniqueNamer = new IsaUniqueNamer();
        private readonly IsaUniqueNamer boogieVarUniqueNamer = new IsaUniqueNamer();
        //use this for concrete Boogie variable names (i.e., ns ''someVariableName'' = ...)
    
        private readonly string funAssmsName = "fun_assms";
        private readonly string varAssmsName = "var_assms";

        private readonly IsaBlockInfo blockInfo;
        private readonly IsaBlockInfo passiveBlockInfo;

        public PrePassiveLemmaManager(
            CFGRepr cfg,
            IDictionary<Block, Block> origToPassiveBlock,
            IsaBlockInfo blockInfo,
            IsaBlockInfo passiveBlockInfo,
            IDictionary<Variable, Variable> passiveToOrigVar,
            IDictionary<Block, IDictionary<Variable, Expr>> constantEntry,
            IDictionary<Block, IDictionary<Variable, Expr>> constantExit,
            BoogieMethodData methodData,
            IVariableTranslationFactory varTranslationFactory)
        {
            this.cfg = cfg;
            this.origToPassiveBlock = origToPassiveBlock;
            passiveToOrigBlock = origToPassiveBlock.ToDictionary((i) => i.Value, (i) => i.Key);
            this.blockInfo = blockInfo;
            this.passiveBlockInfo = passiveBlockInfo;
            this.passiveToOrigVar = passiveToOrigVar;
            this.constantEntry = constantEntry;
            this.constantExit = constantExit;
            this.methodData = methodData;
            programVariables = methodData.InParams.Union(methodData.Locals).Union(methodData.OutParams);
            initState = IsaBoogieTerm.Normal(normalInitState);
            this.varTranslationFactory = varTranslationFactory;
            cmdIsaVisitor = new MultiCmdIsaVisitor(boogieVarUniqueNamer, varTranslationFactory);
            //separate unique namer for function interpretations (since they already have a name in uniqueNamer): possible clashes
            funToInterpMapping = LemmaHelper.FunToTerm(methodData.Functions, new IsaUniqueNamer());

            boogieContext = new BoogieContextIsa(
                IsaCommonTerms.TermIdentFromName("A"),
                IsaCommonTerms.TermIdentFromName("M"),
                IsaCommonTerms.TermIdentFromName("\\<Lambda>"),
                IsaCommonTerms.TermIdentFromName("\\<Gamma>"),
                IsaCommonTerms.TermIdentFromName("\\<Omega>")
                );
        }

        public LemmaDecl GenerateBlockLemma(Block block, IEnumerable<Block> passiveSuc, string lemmaName, string vcHintsName)           
        {
            if (vcHintsName != null)
                throw new ProofGenUnexpectedStateException(GetType(), "did not expect any hints");

            //Term cmds = new TermList(cmdIsaVisitor.Translate(block.Cmds));
            Term cmds = IsaCommonTerms.TermIdentFromName(blockInfo.CmdsQualifiedName(block));
            Term cmdsReduce = IsaBoogieTerm.RedCmdList(boogieContext, cmds, initState, finalState);

            Block origBlock = origToPassiveBlock[block];
            //Term passiveCmds = new TermList(cmdIsaVisitor.Translate(origBlock.Cmds));
            Term passiveCmds = IsaCommonTerms.TermIdentFromName(passiveBlockInfo.CmdsQualifiedName(origBlock));
            Term passiveCmdsReduce = IsaBoogieTerm.RedCmdList(boogieContext, passiveCmds, initState, finalState);
            
            List<Term> assumptions = new List<Term>() { cmdsReduce, passiveCmdsReduce };

            //constantEntry.TryGetValue(block, out IDictionary<Variable, Expr> blockConstEntry);

            //assumptions.AddRange(EntryStateAssumptions(block, normalInitState));

            //conclusion
            //Term conclusion = ConclusionBlock(block, passiveSuc, LemmaHelper.FinalStateIsMagic(block));
            Term conclusion = new BoolConst(true);

            Proof proof = new Proof(new List<string> {"oops"});

            return new LemmaDecl(lemmaName, ContextElem.CreateWithAssumptions(assumptions), conclusion, proof);
        }

        private Term ConstantOptionValue(Expr eConst, Term state)
        {
            throw new NotImplementedException();
            /*
            if(eConst is LiteralExpr lit)
            {
                return IsaCommonTerms.SomeOption(IsaBoogieTerm.ValFromLiteral(lit));
            } else if(eConst is IdentifierExpr id)
            {
                return new TermApp(state, cmdIsaVisitor.TranslateIdentifierExpr(id));
            } else
            {
                throw new ProofGenUnexpectedStateException(this.GetType(), "unexpected constant value");
            }
            */
        }

        public LemmaDecl GenerateEmptyBlockLemma(Block block, IEnumerable<Block> succPassive, string lemmaName)
        {
            /*
            Term cmds = new TermList(cmdIsaVisitor.Translate(block.Cmds));
            Term cmdsReduce = IsaBoogieTerm.RedCmdList(boogieContext, cmds, initState, finalState);
            List<Term> assumptions = new List<Term>() { cmdsReduce };

            assumptions.AddRange(PrunedBlockEntryStateAssms(block, succPassive, normalInitState));

            if (succPassive.Any())
            {
                assumptions.Add(LemmaHelper.ConjunctionOfSuccessorBlocks(succPassive, declToVCMapping, vcinst));
            }

            Term conclusion = ConclusionBlock(block, succPassive);

            Proof proof = BlockCorrectProof(origToPassiveBlock[block], false);

            return new LemmaDecl(lemmaName, ContextElem.CreateWithAssumptions(assumptions), conclusion, proof);
            */
            throw new NotImplementedException();
        }

        public ContextElem Context()
        {
            return new ContextElem(GlobalFixedVariables(), GlobalAssumptions(), AssumptionLabels());
        } 

        public IList<OuterDecl> Prelude()
        {
            var result = new List<OuterDecl>();

            if(programVariables.Any())
            {
                result.Add(new LemmasDecl(varAssmsName, VarAssumptionLabels()));
            }

            if (methodData.Functions.Any())
            {
                result.Add(new LemmasDecl(funAssmsName, FunAssumptionLabels()));
            }

            return result;
        }

        private IList<Term> GlobalAssumptions()
        {
            IList<Term> globalAssms = GlobalVarContextAssumptions();
            globalAssms.AddRange(GlobalFunctionContextAssumptions());
            return globalAssms;
        }

        private IList<Term> GlobalFunctionContextAssumptions()
        {
            throw new NotImplementedException();
            //return LemmaHelper.FunctionAssumptions(methodData.Functions, funToInterpMapping, declToVCMapping, boogieContext.funContext);
        }

        private IList<Term> GlobalVarContextAssumptions()
        {
            throw new NotImplementedException();
            /*
            var assms = new List<Term>();
            foreach (Variable v in programVariables)
            {
                assms.Add(LemmaHelper.VariableTypeAssumption(v, boogieContext.varContext, 
                    new TypeIsaVisitor(varTranslationFactory.CreateTranslation().TypeVarTranslation)));
            }
            return assms;
            */
        }

        private IList<string> AssumptionLabels()
        {
            IList<string> result = VarAssumptionLabels();
            result.AddRange(FunAssumptionLabels());
            return result;
        }

        private IList<string> VarAssumptionLabels()
        {
            return LemmaHelper.AssumptionLabels("V", 0, programVariables.Count());
        }

        private IList<string> FunAssumptionLabels()
        {
            return LemmaHelper.AssumptionLabels("F", programVariables.Count(), 2*methodData.Functions.Count());
        }

        private IList<Tuple<TermIdent, TypeIsa>> GlobalFixedVariables()
        {
            PureTyIsaTransformer pureTyIsaTransformer = new PureTyIsaTransformer();

            VarType absValType = new VarType("a");

            var result = new List<Tuple<TermIdent, TypeIsa>>()
            {
                Tuple.Create((TermIdent) boogieContext.varContext, IsaBoogieType.VarContextType()),
                Tuple.Create((TermIdent) boogieContext.funContext, IsaBoogieType.FunContextType(absValType))
            };

            foreach (KeyValuePair<Function, TermIdent> kv in funToInterpMapping)
            {
                result.Add(Tuple.Create(kv.Value, IsaBoogieType.BoogieFuncInterpType(absValType)));
            }

            return result;
        }

        private List<Term> EntryStateAssumptions(Block block, Term normalState)
        {
            bool constantPred(Variable v) => block.liveVarsBefore.Contains(v);
            var result = ConstantVarAssumptions(block, normalState, constantEntry, constantPred, out ISet<Variable> recordedVars);

            result.AddRange(ActiveVarAssumptions(origToPassiveBlock[block], normalState, (Variable v) => true, out ISet<Variable> newVars));
            recordedVars.UnionWith(newVars);

            bool livePred(Variable v) => !recordedVars.Contains(v);
            result.AddRange(LiveVarAssumptions(block, normalState, livePred, out ISet<Variable> newLiveVars));
            recordedVars.UnionWith(newVars);

            return result;
        }

        private List<Term> PrunedBlockEntryStateAssms(Block block, IEnumerable<Block> bSuccessorsPassive, Term normalState)
        {
            bool constantPred(Variable v) => block.liveVarsBefore.Contains(v);
            var result = ConstantVarAssumptions(block, normalState, constantEntry, constantPred, out ISet<Variable> recordedVars);

            var activeVars = new HashSet<Variable>();
            bool activePred(Variable v) => !activeVars.Contains(v);

            foreach (Block bSuc in bSuccessorsPassive)
            {
                result.AddRange(ActiveVarAssumptions(bSuc, normalState, activePred, out ISet<Variable> newVars));
                activeVars.UnionWith(newVars);
            }

            recordedVars.UnionWith(activeVars);

            bool livePred(Variable v) => !recordedVars.Contains(v);
            result.AddRange(LiveVarAssumptions(block, normalState, livePred, out ISet<Variable> newLiveVars));
            recordedVars.UnionWith(newLiveVars);

            return result;
        }

        private List<Term> ExitStateAssumptions(Block block, IEnumerable<Block> bSuccessorsPassive, Term normalState, out IEnumerable<Variable> boundVars)
        {
            var bSuccessors = cfg.GetSuccessorBlocks(block);

            bool constantPred(Variable v) => bSuccessors.Any(bSuc => bSuc.liveVarsBefore.Contains(v));
            var correctValueAssms = ConstantVarAssumptions(block, normalState, constantExit, constantPred, out ISet<Variable> constantVars);

            var activeVars = new HashSet<Variable>();
            bool activePred(Variable v) => !activeVars.Contains(v);

            foreach (Block bSuc in bSuccessorsPassive)
            {
                correctValueAssms.AddRange(ActiveVarAssumptions(bSuc, normalState, activePred, out ISet<Variable> newVars));
                activeVars.UnionWith(newVars);
            }

            bool livePred(Variable v) => !activeVars.Contains(v) && !constantVars.Contains(v);
            foreach (Block bSuc in bSuccessors)
            {
                correctValueAssms.AddRange(LiveVarAssumptions(bSuc, normalState, livePred, out ISet<Variable> newLiveVars));
                activeVars.UnionWith(newLiveVars);
            }

            boundVars = activeVars;

            return correctValueAssms;
        }

        private List<Term> ConstantVarAssumptions(
            Block b, 
            Term normalState,
            IDictionary<Block, IDictionary<Variable, Expr>> constantInfo, 
            Predicate<Variable> includeVariable,
            out ISet<Variable> includedVars)
        {
            var result = new List<Term>();
            includedVars = new HashSet<Variable>();

            if (constantInfo == null)
                return result;

            if (constantInfo.TryGetValue(b, out IDictionary<Variable, Expr> blockConst))
            {
                foreach (var varAndExp in blockConst)
                {
                    if (includeVariable(varAndExp.Key))
                    {
                        Term rhsTerm = ConstantOptionValue(varAndExp.Value, normalState);
                        result.Add(LemmaHelper.VariableAssumptionExplicit(varAndExp.Key, normalState, rhsTerm, boogieVarUniqueNamer));
                        includedVars.Add(varAndExp.Key);
                    }
                }
            }

            return result;
        }

        private List<Term> ActiveVarAssumptions(Block blockPassive, Term normalState, Predicate<Variable> includeVar, out ISet<Variable> includedVars)
        {
            throw new NotImplementedException();
            /*
            var result = new List<Term>();
            includedVars = new HashSet<Variable>();

            foreach (NamedDeclaration decl in vcinst.GetVCObjParameters(blockPassive))
            {
                if (decl is Variable vPassive)
                {
                    Variable vOrig = passiveToOrigVar[vPassive];

                    if (includeVar(vOrig))
                    {
                        result.Add(LemmaHelper.VariableAssumption(vOrig, normalState, declToVCMapping[vOrig], 
                            varTranslationFactory.CreateTranslation().VarTranslation));
                        includedVars.Add(vOrig);
                    }
                }
            }

            return result;
            */
        }

        //Each variable that is live but not active or constant must map to a correctly typed value
        //this can happen for variables that have not been touched yet, but will be used in the future 
        //such variables are not necessarily active, since they could be universally quantified within some other block     
        private List<Term> LiveVarAssumptions(Block b, Term normalState, Predicate<Variable> includeVar, out ISet<Variable> includedVars)
        {
            throw new NotImplementedException();
            /*
            var result = new List<Term>();
            includedVars = new HashSet<Variable>();

            foreach (Variable v in b.liveVarsBefore)
            {
                if (includeVar(v))
                {
                    result.Add(LemmaHelper.VariableAssumption(v, normalState, declToVCMapping[v], 
                        varTranslationFactory.CreateTranslation().VarTranslation));
                    includedVars.Add(v);
                }
            }
            return result;
            */
        }

        public LemmaDecl MethodVerifiesLemma(CFGRepr cfg2, Term methodCfg, string lemmaName)
        {
            throw new NotImplementedException();
        }
    }
}