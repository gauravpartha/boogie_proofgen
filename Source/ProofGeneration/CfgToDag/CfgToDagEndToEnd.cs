﻿using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.BoogieIsaInterface.VariableTranslation;
using ProofGeneration.CFGRepresentation;
using ProofGeneration.Isa;
using ProofGeneration.PhasesUtil;
using ProofGeneration.Util;

namespace ProofGeneration.CfgToDag
{
    public class CfgToDagEndToEnd
    {
        private IProgramAccessor programAccessor;
        private BoogieContextIsa boogieContext;

        private string varContextName = "\\<Lambda>0";
        
        private readonly string redAssmName = "Red";
        private readonly string vcAssmName = "VC";
        private readonly string closedAssmName = "Closed";
        private readonly string nonEmptyTypesAssmName = "NonEmptyTypes";
        private readonly string finterpAssmName = "FInterp";
        private readonly string axiomAssmName = "Axioms";
        private readonly string preconditionsAssmName = "Precondition";
        private readonly string paramsLocalsAssmName = "ParamsLocal";
        private readonly string constsGlobalsAssmName = "ConstsGlobal";
        private readonly string oldGlobalAssmName = "OldGlobal";
        private readonly string binderEmptyAssmName = "BinderNs";

        private readonly TermIdent normalInitState = IsaCommonTerms.TermIdentFromName("ns");
        private readonly TermIdent finalNodeOrReturn = IsaCommonTerms.TermIdentFromName("m'");
        private readonly TermIdent finalState = IsaCommonTerms.TermIdentFromName("s'");
        
        public IEnumerable<OuterDecl> EndToEndProof(
            string entryCfgLemma,
            string passificationEndToEndLemma,
            Term vcAssm,
            IProgramAccessor programAccessor,
            CFGRepr cfg)
        {
            this.programAccessor = programAccessor;
            boogieContext = new BoogieContextIsa(
                IsaCommonTerms.TermIdentFromName("A"),
                IsaCommonTerms.TermIdentFromName("M"),
                IsaCommonTerms.TermIdentFromName(varContextName),
                IsaCommonTerms.TermIdentFromName("\\<Gamma>"),
                IsaCommonTerms.EmptyList
                );

            var abbrev = new AbbreviationDecl(
                varContextName,
                new Tuple<IList<Term>, Term>(new List<Term>(), new TermTuple(programAccessor.ConstsAndGlobalsDecl(), programAccessor.ParamsAndLocalsDecl()))
            );
            var result = new List<OuterDecl> {abbrev};
            
            Term kStepRed = IsaBoogieTerm.RedCFGKStep(
                BoogieContextIsa.CreateWithNewVarContext(
                    boogieContext,  
                    new TermTuple(programAccessor.ConstsAndGlobalsDecl(), programAccessor.ParamsAndLocalsDecl())
                    ),
                programAccessor.CfgDecl(),
                IsaBoogieTerm.CFGConfigNode(new NatConst(cfg.GetUniqueIntLabel(cfg.entry)), IsaBoogieTerm.Normal(normalInitState)),
                IsaCommonTerms.TermIdentFromName("j"),
                IsaBoogieTerm.CFGConfig(finalNodeOrReturn, finalState)
                );

            StringBuilder proofSb = new StringBuilder();
            proofSb.AppendLine("proof -");
            proofSb.AppendLine("from " + redAssmName + " obtain j where Aux:" + "\""+ kStepRed + "\"");
            proofSb.AppendLine("by (meson rtranclp_imp_relpowp)");
            proofSb.AppendLine("show ?thesis");
            proofSb.AppendLine(ProofUtil.Apply("rule " + entryCfgLemma));
            //TODO: don't hardcode this
            proofSb.AppendLine("unfolding cfg_to_dag_lemmas_def");
            proofSb.AppendLine(ProofUtil.Apply("rule " + finterpAssmName));
            proofSb.AppendLine("apply (rule Aux)");
            proofSb.AppendLine("apply (rule dag_lemma_assms_same)");
            proofSb.AppendLine("unfolding state_well_typed_def");
            proofSb.AppendLine("apply (intro conjI)");
            proofSb.AppendLine("using " + paramsLocalsAssmName + " apply simp");
            proofSb.AppendLine("using " + constsGlobalsAssmName + " apply simp");
            proofSb.AppendLine("using " + constsGlobalsAssmName + " " +  oldGlobalAssmName + " apply simp");
            proofSb.AppendLine("using " + binderEmptyAssmName + " apply simp");
            proofSb.AppendLine(ProofUtil.Apply("rule " + passificationEndToEndLemma));
            //TODO: don't hardcode this
            proofSb.AppendLine("unfolding glue_proof_def");
            proofSb.AppendLine("apply (intro conjI)");
            proofSb.AppendLine("apply assumption");
            proofSb.AppendLine("using " + vcAssmName + " apply simp");
            proofSb.AppendLine("using " + closedAssmName + " apply simp");
            proofSb.AppendLine("using " + nonEmptyTypesAssmName + " apply simp");
            proofSb.AppendLine(ProofUtil.Apply("rule " + finterpAssmName));
            proofSb.AppendLine("using " + axiomAssmName + " apply simp");
            proofSb.AppendLine("using " + paramsLocalsAssmName + " apply simp");
            proofSb.AppendLine("using " + constsGlobalsAssmName + " apply simp");
            proofSb.AppendLine("using " + binderEmptyAssmName + " apply simp");
            proofSb.AppendLine("using " + preconditionsAssmName + " apply simp");
            proofSb.AppendLine("done");
            proofSb.AppendLine("qed");
            
            var lemma = 
                new LemmaDecl(
                "end_to_end_theorem",
                LemmaContext(cfg, vcAssm),
                CfgToDagLemmaManager.CfgLemmaConclusion(boogieContext, programAccessor.PostconditionsDecl(), finalNodeOrReturn, finalState),
                new Proof(new List<string> { proofSb.ToString()})
                );
            result.Add(lemma);
            return result;
        }

        private ContextElem LemmaContext(
            CFGRepr cfg,
            Term vcAssm
            )
        {
            Term multiRed = IsaBoogieTerm.RedCFGMulti(
                BoogieContextIsa.CreateWithNewVarContext(
                    boogieContext,  
                    new TermTuple(programAccessor.ConstsAndGlobalsDecl(), programAccessor.ParamsAndLocalsDecl())
                    ),
                programAccessor.CfgDecl(),
                IsaBoogieTerm.CFGConfigNode(new NatConst(cfg.GetUniqueIntLabel(cfg.entry)), IsaBoogieTerm.Normal(normalInitState)),
                IsaBoogieTerm.CFGConfig(finalNodeOrReturn, finalState)
                );
            Term closedAssm = EndToEndAssumptions.ClosednessAssumption(boogieContext.absValTyMap);
            Term nonEmptyTypesAssm = EndToEndAssumptions.NonEmptyTypesAssumption(boogieContext.absValTyMap);
            Term finterpAssm = IsaBoogieTerm.FunInterpWf(boogieContext.absValTyMap, programAccessor.FunctionsDecl(), boogieContext.funContext);
            var absValType = new VarType("a");
            //need to explicitly give type for normal state, otherwise Isabelle won't know that the abstract value type is the same as used in the VC
            Term axiomAssm = EndToEndAssumptions.AxiomAssumption(boogieContext, programAccessor, new TermWithExplicitType(normalInitState, IsaBoogieType.NormalStateType(absValType)));
            Term presAssm =
                IsaBoogieTerm.ExprAllSat(boogieContext, normalInitState, programAccessor.PreconditionsDecl());
            Term localsAssm = EndToEndAssumptions.LocalStateAssumption(boogieContext, IsaCommonTerms.Snd(boogieContext.varContext), normalInitState);
            Term globalsAssm = EndToEndAssumptions.GlobalStateAssumption(boogieContext, IsaCommonTerms.Fst(boogieContext.varContext), normalInitState);
            Term oldGlobalStateAssm = EndToEndAssumptions.OldGlobalStateAssumption(normalInitState);
            Term binderEmptyAssm = EndToEndAssumptions.BinderStateEmpty(normalInitState);

            return
                ContextElem.CreateWithAssumptions(
                    new List<Term>
                    {
                        multiRed, vcAssm, closedAssm, nonEmptyTypesAssm, finterpAssm, axiomAssm, 
                        presAssm, localsAssm, globalsAssm, oldGlobalStateAssm, binderEmptyAssm
                    },
                    new List<string>
                    {
                        redAssmName, vcAssmName, closedAssmName, nonEmptyTypesAssmName, finterpAssmName, axiomAssmName,
                        preconditionsAssmName, paramsLocalsAssmName, constsGlobalsAssmName, oldGlobalAssmName, binderEmptyAssmName
                    }
                );
        }
    }
}