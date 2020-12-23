using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.BoogieIsaInterface.VariableTranslation;
using ProofGeneration.CFGRepresentation;
using ProofGeneration.Isa;
using ProofGeneration.ProgramToVCProof;
using ProofGeneration.Util;

namespace ProofGeneration.Passification
{
    class PrePassiveLemmaManager 
    {
        private readonly CFGRepr cfg;
        private readonly IDictionary<Block, Block> origToPassiveBlock;

        private readonly PassiveRelationGen _relationGen;

        private readonly BoogieContextIsa boogieContext;
        private readonly TermIdent passiveVarContext;
        
        private readonly TermIdent passiveStates = IsaCommonTerms.TermIdentFromName("U0");
        private readonly TermIdent constrainedVars = IsaCommonTerms.TermIdentFromName("D0");
        private readonly TermIdent stateRel = IsaCommonTerms.TermIdentFromName("R");
        private readonly TermIdent oldStateRel = IsaCommonTerms.TermIdentFromName("R_old");

        private readonly TermIdent normalInitState = IsaCommonTerms.TermIdentFromName("n_s");
        private readonly Term initState;
        private readonly TermIdent finalState = IsaCommonTerms.TermIdentFromName("s'");
        private readonly TermIdent finalNode = IsaCommonTerms.TermIdentFromName("m'");

        private readonly IVariableTranslation<Variable> varTranslation; 
        private readonly IVariableTranslation<Variable> passiveVarTranslation; 

        private readonly IsaUniqueNamer boogieVarUniqueNamer = new IsaUniqueNamer();
        //use this for concrete Boogie variable names (i.e., ns ''someVariableName'' = ...)
    
        private readonly string funAssmsName = "fun_assms";
        private readonly string varAssmsName = "var_assms";

        private readonly IProgramAccessor programAccessor;
        private readonly IProgramAccessor passiveProgramAccessor;

        private readonly Dictionary<Block, int> smallestRequiredVersionDict = new Dictionary<Block, int>();


        public PrePassiveLemmaManager(
            CFGRepr cfg,
            IDictionary<Block, Block> origToPassiveBlock,
            IProgramAccessor programAccessor,
            IProgramAccessor passiveProgramAccessor,
            Tuple<string, string> varContextNonPassivePassive,
            PassiveRelationGen relationGen,
            IVariableTranslationFactory varTranslationFactory,
            IVariableTranslationFactory passiveTranslationFactory)
        {
            this.cfg = cfg;
            this.origToPassiveBlock = origToPassiveBlock;
            this.programAccessor = programAccessor;
            this.passiveProgramAccessor = passiveProgramAccessor;
            this._relationGen = relationGen;
            initState = IsaBoogieTerm.Normal(normalInitState);
            varTranslation = varTranslationFactory.CreateTranslation().VarTranslation;
            passiveVarTranslation = passiveTranslationFactory.CreateTranslation().VarTranslation;
            //separate unique namer for function interpretations (since they already have a name in uniqueNamer): possible clashes

            boogieContext = new BoogieContextIsa(
                IsaCommonTerms.TermIdentFromName("A"),
                IsaCommonTerms.TermIdentFromName("M"),
                IsaCommonTerms.TermIdentFromName(varContextNonPassivePassive.Item1),
                IsaCommonTerms.TermIdentFromName("\\<Gamma>"),
                IsaCommonTerms.TermIdentFromName("\\<Omega>")
                );
            passiveVarContext = IsaCommonTerms.TermIdentFromName(varContextNonPassivePassive.Item2);
        }
        
        //must be called in a topological backwards order
        public Tuple<LemmaDecl,LemmaDecl> GenerateBlockLemma(Block block, string localLemmaName, Func<Block, string> cfgLemmaNameFunc)           
        {
            string cmdsDefName = programAccessor.BlockInfo().CmdsQualifiedName(block);
            Term cmds = IsaCommonTerms.TermIdentFromName(cmdsDefName);

            Block passiveBlock = origToPassiveBlock[block];
            string passiveCmdsDefName = passiveProgramAccessor.BlockInfo().CmdsQualifiedName(passiveBlock);
            Term passiveCmds = IsaCommonTerms.TermIdentFromName(passiveCmdsDefName);
            
            #region compute variable relation update  information
            var successors = cfg.GetSuccessorBlocks(block);
            List<Tuple<Variable,Expr, bool>> varRelUpdates = _relationGen.GenerateVariableRelUpdates(block, out _);

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
            
            //find smallest required version
            int smallestRequired = 1000; //TODO: set to correct initial value
            if (constrainedPassiveVars.Any())
            {
                smallestRequired = constrainedPassiveVars.Select(t => (t as NatConst).n).Min();
            } else if (successors.Any())
            {
                smallestRequired = successors.Select(suc => smallestRequiredVersionDict[suc]).Min();
            }

            smallestRequiredVersionDict[block] = smallestRequired;


            #endregion
            
            var passiveWitness = new PassificationWitness(
                passiveVarContext,
                new TermList(constrainedPassiveVars),
                new TermList(modifiedVarRelTerm),
                stateRel,
                oldStateRel,
                passiveStates,
                constrainedVars);
            
            var stateRelation = _relationGen.GenerateStateRelation(block);
            var stateRelationAssms = new List<Term>();

            foreach (var tupleRel in stateRelation)
            {
                var (origVar, passiveExpr) = tupleRel;
                stateRelationAssms.Add(StateRelAssm(stateRel, origVar, passiveExpr));
            }
            
            #region local block lemma

            List<Term> assumptions = new List<Term>
            {
                IsaBoogieTerm.RedCmdList(boogieContext, cmds, initState, finalState),
                BlockLemmaAssumption(boogieContext, passiveWitness, normalInitState),
            };
            
            assumptions.AddRange(stateRelationAssms);

            //conclusion
            Term conclusion =
                BlockLemmaConclusion(boogieContext, passiveWitness, passiveCmds, finalState);

            var proofMethods =
                new List<string>
                {
                    ProofUtil.Apply("rule passification_block_lemma_compact[OF assms(1-2)]"),
                    "unfolding " + ProofUtil.DefLemma(cmdsDefName) + " " + ProofUtil.DefLemma(passiveCmdsDefName),
                    ProofUtil.Apply("passive_rel_tac " + (stateRelation.Any() ? "R_def: assms(3-)" : "")),
                };
            
            proofMethods.Add("apply (unfold type_rel_def, simp, (intro conjI)?)");
            
            proofMethods.AddRange(
            lookupTyUpdatesLemmas.Select(t => ProofUtil.Apply(ProofUtil.Simp(t.Item1, t.Item2)))
            );
            
            proofMethods.Add("by simp");

            Proof proof = new Proof(proofMethods);

            var localLemma = new LemmaDecl(localLemmaName, ContextElem.CreateWithAssumptions(assumptions), conclusion, proof);
            #endregion
           
            #region cfg lemma
            
            Term redCfg = IsaBoogieTerm.RedCFGMulti(
                boogieContext,
                programAccessor.CfgDecl(),
                IsaBoogieTerm.CFGConfigNode(new NatConst(programAccessor.BlockInfo().BlockIds[block]),
                    IsaBoogieTerm.Normal(normalInitState)),
                IsaBoogieTerm.CFGConfig(finalNode, finalState));
            
            List<Term> cfgAssumptions = new List<Term>
            {
                redCfg,
                CfgBlockLemmaAssumption(boogieContext, passiveWitness, smallestRequired, normalInitState),
            };

            cfgAssumptions.AddRange(stateRelationAssms);

            Term cfgConclusion = CfgLemmaConclusion(
                boogieContext,
                passiveWitness,
                passiveProgramAccessor,
                IsaCommonTerms.Inl(new NatConst(programAccessor.BlockInfo().BlockIds[block])),
                finalState);

            Proof cfgProof = CfgLemmaProof(
                block, 
                localLemmaName, 
                successors.Select(cfgLemmaNameFunc).ToList(),
                stateRelationAssms.Any() 
                );
            
            var cfgLemma = new LemmaDecl(cfgLemmaNameFunc(block), ContextElem.CreateWithAssumptions(cfgAssumptions), cfgConclusion, cfgProof);

            #endregion

            return Tuple.Create(localLemma, cfgLemma);
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
                    rhsValue = IsaCommonTerms.Inr(IsaBoogieTerm.Literal(lit));
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

        public IList<OuterDecl> Prelude()
        {
            var result = new List<OuterDecl>();
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

        private static Term BlockLemmaAssumption(
            BoogieContextIsa boogieContextSource,
            PassificationWitness passificationWitness,
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
                initNonPassiveState
            };
            // IsaCommonTerms.SetUnion(passificationWitness.ConstrainedVariables, passificationWitness.ModifiedVars),
           
            return new TermApp(IsaCommonTerms.TermIdentFromName("passive_lemma_assms"), args);
        }
        
        
        private static Term CfgBlockLemmaAssumption(
            BoogieContextIsa boogieContextSource,
            PassificationWitness passificationWitness,
            int smallestFreeVar,
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
                new NatConst(smallestFreeVar),
                passificationWitness.StateRelation,
                passificationWitness.OldStateRelation,
                passificationWitness.PassiveStates,
                passificationWitness.ConstrainedVariables,
                initNonPassiveState
            };
            // IsaCommonTerms.SetUnion(passificationWitness.ConstrainedVariables, passificationWitness.ModifiedVars),
           
            return new TermApp(IsaCommonTerms.TermIdentFromName("passive_lemma_assms_2"), args);
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
                passificationWitness.OldStateRelation,
                passiveCmds,
                finalState
            };
            // IsaCommonTerms.SetUnion(passificationWitness.ConstrainedVariables, passificationWitness.ModifiedVars),
           
            return new TermApp(IsaCommonTerms.TermIdentFromName("passive_block_conclusion"), args);
        }

        public static Term CfgLemmaConclusion(
            BoogieContextIsa boogieContextSource,
            PassificationWitness passificationWitness,
            IProgramAccessor passiveProgramAccessor,
            Term blockNodeId,
            Term finalState)
        {
            var passiveNormalStateId = new SimpleIdentifier("u");
            var passiveNormalState = new TermIdent(passiveNormalStateId);
            
            var args = new List<Term>
            {
                boogieContextSource.absValTyMap,
                boogieContextSource.methodContext,
                passificationWitness.VarContext,
                boogieContextSource.funContext,
                boogieContextSource.rtypeEnv,
                passiveProgramAccessor.CfgDecl(),
                passiveNormalState,
                blockNodeId
            };
           
            Term sim = new TermApp(IsaCommonTerms.TermIdentFromName("passive_sim_cfg_fail"), args);

            var rhs = TermQuantifier.Exists(
                new List<Identifier> {passiveNormalStateId},
                null,
                TermBinary.And(
                    IsaCommonTerms.Elem(passiveNormalState, passificationWitness.PassiveStates),
                    sim
                    )
                );
            
            return TermBinary.Implies(
                TermBinary.Eq(finalState, IsaBoogieTerm.Failure()), 
                rhs);
        }

        private Proof CfgLemmaProof(Block b, string blockLemmaName, IList<string> successorNames, bool hasStateRelAssms)
        {
            /*
             (tactic ‹cfg_lemma @{context} @{thm assms(1)} @{thm assms(2)} @{thms assms(3-)} 
            (@{thm sync_before_passive_prog.node_1}, @{thm sync_before_passive_prog.outEdges_1})
            (@{thm sync_passive_prog.node_1}, @{thm sync_passive_prog.outEdges_1}) 
            @{thm block_anon4_Then}
            [@{thm cfg_block_anon3}] 1›)
            */
            
            string beforePassiveNodeThm = MLUtil.IsaToMLThm(programAccessor.BlockInfo().BlockCmdsMembershipLemma(b));
            string beforePassiveEdgeThm = MLUtil.IsaToMLThm(programAccessor.BlockInfo().OutEdgesMembershipLemma(b));
            string passiveNodeThm = MLUtil.IsaToMLThm(passiveProgramAccessor.BlockInfo().BlockCmdsMembershipLemma(origToPassiveBlock[b]));
            string passiveEdgeThm = MLUtil.IsaToMLThm(passiveProgramAccessor.BlockInfo().OutEdgesMembershipLemma(origToPassiveBlock[b]));

            var cfgLemmaTacArgs = new List<string>
            {
                MLUtil.ContextAntiquotation(),
                MLUtil.IsaToMLThm("assms(1)"),
                MLUtil.IsaToMLThm("assms(2)"),
                hasStateRelAssms ? MLUtil.IsaToMLThms("assms(3-)") : MLUtil.MLList(new List<string>()),
                MLUtil.MLTuple(beforePassiveNodeThm, beforePassiveEdgeThm),
                MLUtil.MLTuple(passiveNodeThm, passiveEdgeThm),
                MLUtil.IsaToMLThm(blockLemmaName),
                MLUtil.MLList(successorNames.Select(MLUtil.IsaToMLThm))
            };

            var argsString = String.Join(" ", cfgLemmaTacArgs);

            var proofMethods = new List<string>
            {
                ProofUtil.By(ProofUtil.MLTactic("cfg_lemma_tac " + argsString, 1))
            };

            return new Proof(proofMethods);
        }
    }
}
