using System;
using System.Collections;
using System.Collections.Generic;
using System.Linq;
using System.Runtime.CompilerServices;
using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.BoogieIsaInterface.VariableTranslation;
using ProofGeneration.CFGRepresentation;
using ProofGeneration.Isa;
using ProofGeneration.ProgramToVCProof;
using ProofGeneration.Util;

namespace ProofGeneration.Passification
{
    class PrePassiveLemmaManager : IBlockLemmaManager
    {
        private readonly CFGRepr cfg;
        private readonly IDictionary<Block, Block> origToPassiveBlock;
        private readonly IDictionary<Block, Block> passiveToOrigBlock;

        private readonly BoogieMethodData methodData;
        private readonly IEnumerable<Variable> programVariables;

        private readonly PassiveRelationGen _relationGen;

        private readonly BoogieContextIsa boogieContext;
        private readonly string varContextName = "\\<Lambda>1";
        
        private readonly TermIdent passiveVarContext;
        private readonly string passiveVarContextName = "\\<Lambda>2";
        
        private readonly TermIdent passiveStates = IsaCommonTerms.TermIdentFromName("U0");
        private readonly TermIdent constrainedVars = IsaCommonTerms.TermIdentFromName("D0");
        private readonly TermIdent stateRel = IsaCommonTerms.TermIdentFromName("R");
        private readonly TermIdent oldStateRel = IsaCommonTerms.TermIdentFromName("R_old");

        private readonly TermIdent normalInitState = IsaCommonTerms.TermIdentFromName("n_s");
        private readonly Term initState;
        private readonly TermIdent finalState = IsaCommonTerms.TermIdentFromName("s'");

        private readonly IDictionary<Function, TermIdent> funToInterpMapping;

        private readonly MultiCmdIsaVisitor cmdIsaVisitor;

        private readonly IVariableTranslationFactory varTranslationFactory;

        private readonly IVariableTranslation<Variable> varTranslation; 
        private readonly IVariableTranslation<Variable> passiveVarTranslation; 

        private readonly IsaUniqueNamer uniqueNamer = new IsaUniqueNamer();
        private readonly IsaUniqueNamer boogieVarUniqueNamer = new IsaUniqueNamer();
        //use this for concrete Boogie variable names (i.e., ns ''someVariableName'' = ...)
    
        private readonly string funAssmsName = "fun_assms";
        private readonly string varAssmsName = "var_assms";

        private readonly IsaBlockInfo blockInfo;
        private readonly IProgramAccessor programAccessor;
        private readonly IsaBlockInfo passiveBlockInfo;
        private readonly IProgramAccessor passiveProgramAccessor;


        public PrePassiveLemmaManager(
            CFGRepr cfg,
            IDictionary<Block, Block> origToPassiveBlock,
            IsaBlockInfo blockInfo,
            IProgramAccessor programAccessor,
            IsaBlockInfo passiveBlockInfo,
            IProgramAccessor passiveProgramAccessor,
            PassificationHintManager hintManager,
            IDictionary<Block, IDictionary<Variable,Expr>> initialVarMapping,
            BoogieMethodData methodData,
            IVariableTranslationFactory varTranslationFactory,
            IVariableTranslationFactory passiveTranslationFactory)
        {
            this.cfg = cfg;
            this.origToPassiveBlock = origToPassiveBlock;
            passiveToOrigBlock = origToPassiveBlock.ToDictionary((i) => i.Value, (i) => i.Key);
            this.blockInfo = blockInfo;
            this.programAccessor = programAccessor;
            this.passiveBlockInfo = passiveBlockInfo;
            this.passiveProgramAccessor = passiveProgramAccessor;
            this._relationGen = new PassiveRelationGen(hintManager, initialVarMapping, origToPassiveBlock);
            this.methodData = methodData;
            programVariables = methodData.InParams.Union(methodData.Locals);
            initState = IsaBoogieTerm.Normal(normalInitState);
            this.varTranslationFactory = varTranslationFactory;
            varTranslation = varTranslationFactory.CreateTranslation().VarTranslation;
            passiveVarTranslation = passiveTranslationFactory.CreateTranslation().VarTranslation;
            cmdIsaVisitor = new MultiCmdIsaVisitor(boogieVarUniqueNamer, varTranslationFactory);
            //separate unique namer for function interpretations (since they already have a name in uniqueNamer): possible clashes
            funToInterpMapping = LemmaHelper.FunToTerm(methodData.Functions, new IsaUniqueNamer());

            boogieContext = new BoogieContextIsa(
                IsaCommonTerms.TermIdentFromName("A"),
                IsaCommonTerms.TermIdentFromName("M"),
                IsaCommonTerms.TermIdentFromName(varContextName),
                IsaCommonTerms.TermIdentFromName("\\<Gamma>1"),
                IsaCommonTerms.TermIdentFromName("\\<Omega>")
                );
            passiveVarContext = IsaCommonTerms.TermIdentFromName(passiveVarContextName);
        }

        public LemmaDecl GenerateBlockLemma(Block block, IEnumerable<Block> successors, string lemmaName, string vcHintsName)           
        {
            if (vcHintsName != null)
                throw new ProofGenUnexpectedStateException(GetType(), "did not expect any hints");

            string cmdsDefName = blockInfo.CmdsQualifiedName(block);
            Term cmds = IsaCommonTerms.TermIdentFromName(cmdsDefName);

            Block passiveBlock = origToPassiveBlock[block];
            string passiveCmdsDefName = passiveBlockInfo.CmdsQualifiedName(passiveBlock);
            Term passiveCmds = IsaCommonTerms.TermIdentFromName(passiveCmdsDefName);
            
            List<Tuple<Variable,Expr, bool>> varRelUpdates = _relationGen.GenerateVariableRelUpdates(block, passiveBlock, successors, out _);

            List<Term> constrainedPassiveVars = new List<Term>();
            List<Term> modifiedVarRelTerm = new List<Term>();
            List<Tuple<string, string>> lookupTyUpdatesLemmas = new List<Tuple<string, string>>();

            foreach (var tuple in varRelUpdates)
            {
                var origVar = tuple.Item1;
                if (varTranslation.TryTranslateVariableId(origVar, out var origVarTerm, out _))
                {
                    if (tuple.Item2 is IdentifierExpr ie)
                    {
                        var passiveVar = ie.Decl;
                        if (passiveVarTranslation.TryTranslateVariableId(passiveVar, out var passiveVarTerm, out _))
                        {
                            modifiedVarRelTerm.Add(new TermTuple(origVarTerm, IsaCommonTerms.Inl(passiveVarTerm)));
                            /* don't add variable to newly constrained variables if update is associated with constant propagation
                             * in which case the variable is not newly constrained */
                            if (!tuple.Item3)
                            {
                                constrainedPassiveVars.Add(passiveVarTerm);
                            }
                            lookupTyUpdatesLemmas.Add(
                                Tuple.Create(programAccessor.LookupVarTyLemma(origVar), passiveProgramAccessor.LookupVarTyLemma(passiveVar))
                                );
                        }
                        else
                        {
                            throw new ProofGenUnexpectedStateException(GetType(), "Could not translate variables.");
                        }
                    }
                    else if (tuple.Item2 is LiteralExpr lit)
                    {
                        Term litTerm = IsaBoogieTerm.Literal(lit);
                        modifiedVarRelTerm.Add(new TermTuple(origVarTerm, IsaCommonTerms.Inr(litTerm)));
                    }
                    else
                    {
                        throw new ProofGenUnexpectedStateException(GetType(),
                            "Unexpected orig variable to passive expression mapping");
                    }
                }
                else
                {
                    throw new ProofGenUnexpectedStateException(GetType(), "Could not translate variables.");
                }
            }
            
            var passiveWitness = new PassificationWitness(
                passiveVarContext,
                new TermList(constrainedPassiveVars),
                new TermList(modifiedVarRelTerm),
                stateRel,
                oldStateRel,
                passiveStates,
                constrainedVars);

            List<Term> assumptions = new List<Term>
            {
                IsaBoogieTerm.RedCmdList(boogieContext, cmds, initState, finalState),
                BlockLemmaAssumption(boogieContext, passiveWitness, cmds, normalInitState),
            };

            var stateRelation = _relationGen.GenerateStateRelation(block);

            foreach (var tupleRel in stateRelation)
            {
                var (origVar, passiveExpr) = tupleRel;
                assumptions.Add(StateRelAssm(stateRel, origVar, passiveExpr));
            }

            //constantEntry.TryGetValue(block, out IDictionary<Variable, Expr> blockConstEntry);

            //assumptions.AddRange(EntryStateAssumptions(block, normalInitState));

            //conclusion
            Term conclusion =
                BlockLemmaConclusion(boogieContext, passiveWitness, passiveCmds, finalState);

            var proofMethods =
                new List<string>
                {
                    ProofUtil.Apply("rule passification_block_lemma_compact[OF assms(1-2)]"),
                    "unfolding " + ProofUtil.DefLemma(cmdsDefName) + " " + ProofUtil.DefLemma(passiveCmdsDefName),
                    ProofUtil.Apply("passive_rel_tac R_def: assms(3-)"),
                };
            
            proofMethods.Add("apply (unfold type_rel_def, simp, (intro conjI)?)");
            
            proofMethods.AddRange(
            lookupTyUpdatesLemmas.Select(t => ProofUtil.Apply(ProofUtil.Simp(t.Item1, t.Item2)))
            );
            
            proofMethods.Add("by simp");

            Proof proof = new Proof(proofMethods);

            return new LemmaDecl(lemmaName, ContextElem.CreateWithAssumptions(assumptions), conclusion, proof);
        }

        private Term StateRelAssm(Term stateRelation, Variable origVar, Expr passiveExpr)
        {
            if (varTranslation.TryTranslateVariableId(origVar, out Term origVarTerm, out _))
            {
                Term rhsValue;
                if (passiveExpr is IdentifierExpr ie)
                {
                    if (passiveVarTranslation.TryTranslateVariableId(ie.Decl, out Term passiveVarTerm, out _))
                    {
                        rhsValue = IsaCommonTerms.Inl(passiveVarTerm);
                    }
                    else
                    {
                        throw new ProofGenUnexpectedStateException(GetType(), "can't translate variable");
                    }
                } else if (passiveExpr is LiteralExpr lit)
                {
                    rhsValue = IsaCommonTerms.Inr(cmdIsaVisitor.Translate(lit).First());
                }
                else
                {
                    throw new ProofGenUnexpectedStateException(GetType(), "unsupported passive expression");    
                }

                return TermBinary.Eq(
                    new TermApp(stateRelation, origVarTerm), 
                    IsaCommonTerms.SomeOption(rhsValue));
            }
            else
            {
                throw new ProofGenUnexpectedStateException(GetType(), "unsupported passive expression");    
            }
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
            
            var varContextAbbrev = new AbbreviationDecl(
                varContextName,
                new Tuple<IList<Term>, Term>(new List<Term>(), programAccessor.VarContext())
                );
            
            var passiveVarContextAbbrev = new AbbreviationDecl(
                passiveVarContextName,
                new Tuple<IList<Term>, Term>(new List<Term>(), passiveProgramAccessor.VarContext())
                );
            
            result.Add(varContextAbbrev);
            result.Add(passiveVarContextAbbrev);
            
            /*
            if(programVariables.Any())
            {
                result.Add(new LemmasDecl(varAssmsName, VarAssumptionLabels()));
            }

            if (methodData.Functions.Any())
            {
                result.Add(new LemmasDecl(funAssmsName, FunAssumptionLabels()));
            }
            */
            
            result.Add(new DeclareDecl("One_nat_def[simp del]"));

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
            VarType absValType = new VarType("a");

            var result = new List<Tuple<TermIdent, TypeIsa>>
            {
                Tuple.Create((TermIdent) boogieContext.varContext, IsaBoogieType.VarContextType()),
                Tuple.Create((TermIdent) boogieContext.funContext, IsaBoogieType.FunInterpType(absValType))
            };

            foreach (KeyValuePair<Function, TermIdent> kv in funToInterpMapping)
            {
                result.Add(Tuple.Create(kv.Value, IsaBoogieType.BoogieFuncInterpType(absValType)));
            }

            return result;
        }

        private static Term BlockLemmaAssumption(
            BoogieContextIsa boogieContextSource,
            PassificationWitness passificationWitness,
            Term nonPassiveCmds,
            Term initNonPassiveState)
        {
            var args = new List<Term>
            {
                boogieContextSource.absValTyMap,
                boogieContextSource.methodContext,
                boogieContextSource.varContext,
                passificationWitness.VarContext,
                boogieContextSource.funContext,
                boogieContextSource.rtypeEnv,
                passificationWitness.ModifiedVars,
                passificationWitness.StateRelation,
                passificationWitness.OldStateRelation,
                passificationWitness.PassiveStates,
                passificationWitness.ConstrainedVariables,
                nonPassiveCmds,
                initNonPassiveState
            };
            // IsaCommonTerms.SetUnion(passificationWitness.ConstrainedVariables, passificationWitness.ModifiedVars),
           
            return new TermApp(IsaCommonTerms.TermIdentFromName("passive_lemma_assms"), args);
        }
            
        private static Term BlockLemmaConclusion(
            BoogieContextIsa boogieContextSource,
            PassificationWitness passificationWitness,
            Term passiveCmds,
            Term finalState)
        {
            var args = new List<Term>
            {
                boogieContextSource.absValTyMap,
                boogieContextSource.methodContext,
                boogieContextSource.varContext,
                passificationWitness.VarContext,
                boogieContextSource.funContext,
                boogieContextSource.rtypeEnv,
                passificationWitness.PassiveStates,
                IsaCommonTerms.SetUnion(passificationWitness.ConstrainedVariables, 
                    IsaCommonTerms.SetOfList(passificationWitness.ModifiedVars)),
                new TermApp(IsaCommonTerms.TermIdentFromName("update_nstate_rel"), 
                    passificationWitness.StateRelation,
                    passificationWitness.ModifiedVarsRelation),
                passiveCmds,
                finalState
            };
            // IsaCommonTerms.SetUnion(passificationWitness.ConstrainedVariables, passificationWitness.ModifiedVars),
           
            return new TermApp(IsaCommonTerms.TermIdentFromName("passive_block_conclusion"), args);
        }

        /*
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
        */

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
