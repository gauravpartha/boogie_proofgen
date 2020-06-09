using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.CFGRepresentation;
using ProofGeneration.Isa;
using ProofGeneration.Util;
using ProofGeneration.VCProofGen;

namespace ProofGeneration.ProgramToVCProof
{
    class PrePassiveLemmaManager : IBlockLemmaManager
    {
        private readonly VCInstantiation vcinst;
        private readonly CFGRepr cfg;
        private readonly IDictionary<Block, Block> origToPassiveBlock;
        private readonly IDictionary<Block, Block> passiveToOrigBlock;

        private readonly IDictionary<Variable, Variable> passiveToOrigVar;
        private readonly IDictionary<Block, IDictionary<Variable, Expr>> constantEntry;
        private readonly IDictionary<Block, IDictionary<Variable, Expr>> constantExit;


        private readonly IEnumerable<Function> functions;
        private readonly IEnumerable<Variable> programVariables;

        private readonly TermIdent varContext = IsaCommonTerms.TermIdentFromName("\\<Lambda>");
        private readonly TermIdent functionContext = IsaCommonTerms.TermIdentFromName("\\<Gamma>");
        private readonly TermIdent normalInitState = IsaCommonTerms.TermIdentFromName("n_s");
        private readonly Term initState;
        private readonly TermIdent finalState = IsaCommonTerms.TermIdentFromName("s'");

        private readonly IDictionary<NamedDeclaration, TermIdent> declToVCMapping;        

        private readonly IDictionary<Function, TermIdent> funToInterpMapping;

        private readonly MultiCmdIsaVisitor cmdIsaVisitor;

        private readonly IsaUniqueNamer uniqueNamer = new IsaUniqueNamer();
        private readonly IsaUniqueNamer boogieVarUniqueNamer = new IsaUniqueNamer();
        //use this for concrete Boogie variable names (i.e., ns ''someVariableName'' = ...)
    
        private readonly string funAssmsName = "fun_assms";
        private readonly string varAssmsName = "var_assms";

        public PrePassiveLemmaManager(
            VCInstantiation vcinst,
            CFGRepr cfg,
            IDictionary<Block, Block> origToPassiveBlock,
            IDictionary<Variable, Variable> passiveToOrigVar,
            IDictionary<Block, IDictionary<Variable, Expr>> constantEntry,
            IDictionary<Block, IDictionary<Variable, Expr>> constantExit,
            IEnumerable<Function> functions, 
            IEnumerable<Variable> inParams,
            IEnumerable<Variable> outParams,
            IEnumerable<Variable> localVars)
        {
            this.vcinst = vcinst;
            this.cfg = cfg;
            this.origToPassiveBlock = origToPassiveBlock;
            passiveToOrigBlock = origToPassiveBlock.ToDictionary((i) => i.Value, (i) => i.Key);
            this.passiveToOrigVar = passiveToOrigVar;
            this.constantEntry = constantEntry;
            this.constantExit = constantExit;
            this.functions = functions;
            programVariables = inParams.Union(localVars).Union(outParams);
            initState = IsaBoogieTerm.Normal(normalInitState);        
            cmdIsaVisitor = new MultiCmdIsaVisitor(boogieVarUniqueNamer);
            declToVCMapping = LemmaHelper.DeclToTerm(((IEnumerable<NamedDeclaration>)functions).Union(programVariables).Union(localVars), uniqueNamer);
            //separate unique namer for function interpretations (since they already have a name in uniqueNamer): possible clashes
            funToInterpMapping = LemmaHelper.FunToTerm(functions, new IsaUniqueNamer());
        }

        public LemmaDecl GenerateBlockLemma(Block block, IEnumerable<Block> passiveSuc, string lemmaName, string vcHintsName)           
        {
            if (vcHintsName != null)
                throw new ProofGenUnexpectedStateException(GetType(), "did not expect any hints");

            Term cmds = new TermList(cmdIsaVisitor.Translate(block.Cmds));
            Term cmdsReduce = IsaBoogieTerm.RedCmdList(varContext, functionContext, cmds, initState, finalState);

            List<Term> assumptions = new List<Term>() { cmdsReduce };

            Block origBlock = origToPassiveBlock[block];

            constantEntry.TryGetValue(block, out IDictionary<Variable, Expr> blockConstEntry);

            assumptions.AddRange(EntryStateAssumptions(block, normalInitState));

            //add VC assumption
            assumptions.Add(
                vcinst.GetVCBlockInstantiation(origBlock, passiveDecl =>
                {
                    if (passiveDecl is Function)
                    {
                        return declToVCMapping[passiveDecl];
                    }
                    else
                    {
                        return declToVCMapping[passiveToOrigVar[(Variable)passiveDecl]];
                    }
                }
                )
            );

            //conclusion
            Term conclusion = ConclusionBlock(block, passiveSuc, LemmaHelper.FinalStateIsMagic(block));

            return new LemmaDecl(lemmaName, ContextElem.CreateWithAssumptions(assumptions), conclusion, BlockCorrectProof(origBlock, true));
        }

        private Proof BlockCorrectProof(Block b, bool unfoldVC)
        {
            List<string> methods = new List<string>
            {
                "using assms " + (functions.Any() ? funAssmsName : ""),
                "apply cases"
            };

            if (unfoldVC)
                methods.Add("apply (simp only: " + vcinst.GetVCBlockNameRef(b) + "_def)");

            methods.Add("apply (handle_cmd_list_full v_assms: " + varAssmsName + ")?");
            methods.Add("by (auto?)");

            return new Proof(methods);
        }

        private Term ConstantOptionValue(Expr eConst, Term state)
        {
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
        }

        public LemmaDecl GenerateEmptyBlockLemma(Block block, IEnumerable<Block> succPassive, string lemmaName)
        {
            Term cmds = new TermList(cmdIsaVisitor.Translate(block.Cmds));
            Term cmdsReduce = IsaBoogieTerm.RedCmdList(varContext, functionContext, cmds, initState, finalState);
            List<Term> assumptions = new List<Term>() { cmdsReduce };

            assumptions.AddRange(PrunedBlockEntryStateAssms(block, succPassive, normalInitState));

            if (succPassive.Any())
            {
                assumptions.Add(LemmaHelper.ConjunctionOfSuccessorBlocks(succPassive, declToVCMapping, vcinst));
            }

            Term conclusion = ConclusionBlock(block, succPassive);

            Proof proof = BlockCorrectProof(origToPassiveBlock[block], false);

            return new LemmaDecl(lemmaName, ContextElem.CreateWithAssumptions(assumptions), conclusion, proof);
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

            if (functions.Any())
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
            return LemmaHelper.FunctionAssumptions(functions, funToInterpMapping, declToVCMapping, functionContext);
        }

        private IList<Term> GlobalVarContextAssumptions()
        {
            var assms = new List<Term>();
            foreach (Variable v in programVariables)
            {
                assms.Add(LemmaHelper.VariableTypeAssumption(v, varContext, boogieVarUniqueNamer));
            }
            return assms;
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
            return LemmaHelper.AssumptionLabels("F", programVariables.Count(), 2*functions.Count());
        }

        private IList<Tuple<TermIdent, TypeIsa>> GlobalFixedVariables()
        {
            PureTyIsaTransformer pureTyIsaTransformer = new PureTyIsaTransformer();

            var result = new List<Tuple<TermIdent, TypeIsa>>()
            {
                Tuple.Create(varContext, IsaBoogieType.VarContextType()),
                Tuple.Create(functionContext, IsaBoogieType.FunContextType())
            };

            foreach (KeyValuePair<Function, TermIdent> kv in funToInterpMapping)
            {
                result.Add(Tuple.Create(kv.Value, IsaBoogieType.BoogieFuncInterpType()));
            }

            return result;
        }

        private Term ConclusionBlock(Block b,
            IEnumerable<Block> passiveSuc,
            bool useMagicFinalState = false)
        {
            if (useMagicFinalState)
                return new TermBinary(finalState, IsaBoogieTerm.Magic(), TermBinary.BinaryOpCode.EQ);

            Term nonFailureConclusion = new TermBinary(finalState, IsaBoogieTerm.Failure(), TermBinary.BinaryOpCode.NEQ);

            var bSuccessors = cfg.GetSuccessorBlocks(b);

            if (!bSuccessors.Any())
            {
                if(passiveSuc.Any())
                {
                    throw new ProofGenUnexpectedStateException(this.GetType(), "at least one passive successor but no actual successors");
                }
                return nonFailureConclusion;
            }

            TermIdent normalFinalState = IsaCommonTerms.TermIdentFromName("n_s'");

            Term ifNormalConclusionLhs = new TermBinary(finalState, IsaBoogieTerm.Normal(normalFinalState), TermBinary.BinaryOpCode.EQ);


            var correctValues = ExitStateAssumptions(b, passiveSuc, normalFinalState, out IEnumerable<Variable> boundVars);

            var successorVCs = new List<Term>();
            foreach (Block bSuc in passiveSuc)
            {
                //successor vc
                successorVCs.Add(
                    vcinst.GetVCBlockInstantiation(bSuc, passiveDecl =>
                    {
                        if (passiveDecl is Function)
                            return declToVCMapping[passiveDecl];
                        else
                            return declToVCMapping[passiveToOrigVar[(Variable)passiveDecl]];
                    }
                ));
            }

            if(!correctValues.Any() && !successorVCs.Any())
            {
                return nonFailureConclusion;
            }
            
            Term ifNormalConclusionRhs;
            if(correctValues.Any())
            {
                Term GetRHS(Term sucVCTerm)
                {
                    Term activeCorrectValuesCollect = LemmaHelper.BinaryOpAggregate(correctValues, TermBinary.BinaryOpCode.AND);
                    Term ifNormalConclusionRhsBody =
                      (sucVCTerm != null ? new TermBinary(activeCorrectValuesCollect, sucVCTerm, TermBinary.BinaryOpCode.AND)
                                         : activeCorrectValuesCollect)
                        ;
                    if (boundVars.Any())
                    {
                        return
                            new TermQuantifier(TermQuantifier.QuantifierKind.EX,
                            boundVars.Select(v => declToVCMapping[v].id).ToList(),
                            ifNormalConclusionRhsBody
                        );
                    }
                    else
                    {
                        return ifNormalConclusionRhsBody;
                    }
                }

                if (successorVCs.Any())
                {
                    Term successorVCsCollect = LemmaHelper.BinaryOpAggregate(successorVCs, TermBinary.BinaryOpCode.AND);
                    ifNormalConclusionRhs = GetRHS(successorVCsCollect);
                } else
                {
                    ifNormalConclusionRhs = GetRHS(null);
                }
            }
            else
            {
                ifNormalConclusionRhs = LemmaHelper.BinaryOpAggregate(successorVCs, TermBinary.BinaryOpCode.AND);
            }

            Term ifNormalConclusion =
                new TermQuantifier(
                    TermQuantifier.QuantifierKind.ALL,
                    new List<Identifier>() { normalFinalState.id },
                    new TermBinary(
                        ifNormalConclusionLhs,
                        ifNormalConclusionRhs,
                        TermBinary.BinaryOpCode.IMPLIES)
                    );

            return new TermBinary(nonFailureConclusion, ifNormalConclusion, TermBinary.BinaryOpCode.AND);
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
            var result = new List<Term>();
            includedVars = new HashSet<Variable>();

            foreach (NamedDeclaration decl in vcinst.GetVCBlockParameters(blockPassive))
            {
                if (decl is Variable vPassive)
                {
                    Variable vOrig = passiveToOrigVar[vPassive];

                    if (includeVar(vOrig))
                    {
                        result.Add(LemmaHelper.VariableAssumption(vOrig, normalState, declToVCMapping[vOrig], boogieVarUniqueNamer));
                        includedVars.Add(vOrig);
                    }
                }
            }

            return result;
        }

        //Each variable that is live but not active or constant must map to a correctly typed value
        //this can happen for variables that have not been touched yet, but will be used in the future 
        //such variables are not necessarily active, since they could be universally quantified within some other block     
        private List<Term> LiveVarAssumptions(Block b, Term normalState, Predicate<Variable> includeVar, out ISet<Variable> includedVars)
        {
            var result = new List<Term>();
            includedVars = new HashSet<Variable>();

            foreach (Variable v in b.liveVarsBefore)
            {
                if (includeVar(v))
                {
                    result.Add(LemmaHelper.VariableAssumption(v, normalState, declToVCMapping[v], boogieVarUniqueNamer));
                    includedVars.Add(v);
                }
            }
            return result;
        }


    }
}
