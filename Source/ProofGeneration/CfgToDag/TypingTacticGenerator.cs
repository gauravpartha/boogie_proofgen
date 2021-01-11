﻿using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.BoogieIsaInterface.VariableTranslation;
using ProofGeneration.Isa;
using ProofGeneration.Util;

namespace ProofGeneration.CfgToDag
{
    public class TypingTacticGenerator
    {
        private readonly FunctionCollector functionCollector = new FunctionCollector();
        private readonly EqualityHintGenerator equalityHintGenerator;
        private readonly IProgramAccessor programAccessor;

        public TypingTacticGenerator(IProgramAccessor programAccessor, IVariableTranslationFactory factory)
        {
           equalityHintGenerator = new EqualityHintGenerator(factory); 
        }
        
        public Tuple<string, IEnumerable<LemmaDecl>> GenerateTactic(Expr e)
        {
            VariableCollector varCollector = new VariableCollector();
            varCollector.Visit(e);
            
            var lookupTyThms = new List<string>();
            var funMemThms = new List<string>();

            foreach (Variable v in varCollector.usedVars)
            {
                try
                {
                    lookupTyThms.Add(programAccessor.LookupVarTyLemma(v));
                }
                catch
                {
                    //variable not found, possible if, for example, v is bound
                }
            }

            var usedFuncs = functionCollector.UsedFunctions(e);
            foreach (Function f in usedFuncs)
            {
                funMemThms.Add(programAccessor.MembershipLemma(f));
            }

            var hintLemmas = equalityHintGenerator.GetHints(e);

            var hintsML = MLUtil.IsaToMLThms(hintLemmas.Select(lemma => lemma.name));
            var lookupTyML = MLUtil.IsaToMLThms(lookupTyThms);
            var funMemML = MLUtil.IsaToMLThms(funMemThms);

            var args = new List<string>
            {
                MLUtil.ContextAntiquotation(),
                hintsML,
                lookupTyML,
                funMemML
            };

            string tactic = ProofUtil.Apply(ProofUtil.MLTactic("typing_tac " + String.Join(" ", args), 1));

            return Tuple.Create(tactic, hintLemmas);
        }
    }
}