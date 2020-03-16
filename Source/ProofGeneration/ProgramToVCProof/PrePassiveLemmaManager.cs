using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.Isa;
using ProofGeneration.Util;
using ProofGeneration.VCProofGen;

namespace ProofGeneration.ProgramToVCProof
{
    class PrePassiveLemmaManager : IBlockLemmaManager
    {
        private readonly VCInstantiation vcinst;
        private readonly IDictionary<Block, Block> origToPassiveBlock;
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
            IDictionary<Block, Block> origToPassiveBlock,
            IDictionary<Variable, Variable> passiveToOrigVar,
            IEnumerable<Function> functions, 
            IEnumerable<Variable> inParams,
            IEnumerable<Variable> outParams,
            IEnumerable<Variable> localVars)
        {
            this.vcinst = vcinst;
            this.origToPassiveBlock = origToPassiveBlock;
            this.passiveToOrigVar = passiveToOrigVar;
            this.functions = functions;
            programVariables = inParams.Union(localVars).Union(outParams);
            initState = IsaBoogieTerm.Normal(normalInitState);        
            cmdIsaVisitor = new MultiCmdIsaVisitor(boogieVarUniqueNamer);
            declToVCMapping = LemmaHelper.DeclToTerm(((IEnumerable<NamedDeclaration>)functions).Union(programVariables).Union(localVars), uniqueNamer);
            funToInterpMapping = LemmaHelper.FunToTerm(functions, uniqueNamer);
        }

        public LemmaDecl GenerateBlockLemma(Block block, IEnumerable<Block> successors, string lemmaName)
        {
            Term cmds = new TermList(cmdIsaVisitor.Translate(block.Cmds));
            Term cmdsReduce = IsaBoogieTerm.RedCmdList(varContext, functionContext, cmds, initState, finalState);

            List<Term> assumptions = new List<Term>() { cmdsReduce };

            Block origBlock = origToPassiveBlock[block];

            //For each active passive variable in the current block, assume that the corresponding original variable maps to a properly typed value
            foreach (NamedDeclaration decl in vcinst.GetVCBlockParameters(origBlock))
            {
                if(decl is Variable vPassive)
                {
                    Variable vOrig = passiveToOrigVar[vPassive];
                    assumptions.Add(LemmaHelper.VariableAssumption(vOrig, normalInitState, declToVCMapping[vOrig], boogieVarUniqueNamer));
                }
            }

            //add VC assumption
            assumptions.Add(
                vcinst.GetVCBlockInstantiation(origBlock, passiveDecl =>
                {
                    if (passiveDecl is Function)
                        return declToVCMapping[passiveDecl];
                    else
                        return declToVCMapping[passiveToOrigVar[(Variable)passiveDecl]];
                }
                )
            );

            //conclusion
            Term conclusion = ConclusionBlock(block, successors, LemmaHelper.FinalStateIsMagic(block));

            return new LemmaDecl(lemmaName, ContextElem.CreateWithAssumptions(assumptions), conclusion, new Proof(new List<string>() { "oops" }));
        }

        public LemmaDecl GenerateEmptyBlockLemma(Block block, IEnumerable<Block> successors, string lemmaName)
        {
            Term cmds = new TermList(cmdIsaVisitor.Translate(block.Cmds));
            Term cmdsReduce = IsaBoogieTerm.RedCmdList(varContext, functionContext, cmds, initState, finalState);
            List<Term> assumptions = new List<Term>() { cmdsReduce };
            Term conclusion = ConclusionBlock(block, successors);

            Proof proof = new Proof(
                    new List<string>()
                    {
                                    "using assms",
                                    "apply cases",
                                    "by auto"
                    }
                  );

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
            return LemmaHelper.AssumptionLabels("F", programVariables.Count(), functions.Count());
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
            IEnumerable<Block> b_successors,
            bool useMagicFinalState = false)
        {
            if (useMagicFinalState)
                return new TermBinary(finalState, IsaBoogieTerm.Magic(), TermBinary.BinaryOpCode.EQ);

            Term nonFailureConclusion = new TermBinary(finalState, IsaBoogieTerm.Failure(), TermBinary.BinaryOpCode.NEQ);

            if (!b_successors.Any())
                return nonFailureConclusion;

            TermIdent normalFinalState = IsaCommonTerms.TermIdentFromName("n_s'");


            Term ifNormalConclusionLhs = new TermBinary(finalState, IsaBoogieTerm.Normal(normalFinalState), TermBinary.BinaryOpCode.EQ);

            var activeVars = new HashSet<Variable>();
            var activeCorrectValues = new HashSet<Term>();
            var successorVCs = new List<Term>();

            foreach(Block bSuc in b_successors)
            {
                successorVCs.Add(
                    vcinst.GetVCBlockInstantiation(bSuc, passiveDecl =>
                    {
                        if (passiveDecl is Function)
                            return declToVCMapping[passiveDecl];
                        else
                            return declToVCMapping[passiveToOrigVar[(Variable)passiveDecl]];
                    }
                ));

                foreach (NamedDeclaration activeSuccDecl in vcinst.GetVCBlockParameters(bSuc))
                {
                    if(activeSuccDecl is Variable activeSuccVar)
                    {
                        Variable origVar = passiveToOrigVar[activeSuccVar];
                        if(!activeVars.Contains(origVar))
                        {
                            //active vars map to correctly typed value
                            activeCorrectValues.Add(LemmaHelper.VariableAssumption(origVar, normalFinalState, declToVCMapping[origVar], boogieVarUniqueNamer));
                            activeVars.Add(origVar);
                        }
                    }
                }
            }
            Term successorVCsCollect = LemmaHelper.BinaryOpAggregate(successorVCs, TermBinary.BinaryOpCode.AND);

            Term ifNormalConclusionRhs;
            if(activeVars.Any())
            {
                Term activeCorrectValuesCollect = LemmaHelper.BinaryOpAggregate(activeCorrectValues, TermBinary.BinaryOpCode.AND);
                Term ifNormalConclusionRhsBody =
                    new TermBinary(activeCorrectValuesCollect, successorVCsCollect, TermBinary.BinaryOpCode.AND);
                ifNormalConclusionRhs =
                    new TermQuantifier(TermQuantifier.QuantifierKind.EX,
                    activeVars.Select(v => declToVCMapping[v].id).ToList(),
                    ifNormalConclusionRhsBody
                );
            } else
            {
                ifNormalConclusionRhs = successorVCsCollect;
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
    }
}
