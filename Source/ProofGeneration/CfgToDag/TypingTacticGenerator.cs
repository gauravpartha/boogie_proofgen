using System;
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
        private readonly EqualityHintGenerator equalityHintGenerator;
        private readonly FunctionCollector functionCollector = new FunctionCollector();
        private readonly IProgramAccessor programAccessor;

        public TypingTacticGenerator(IProgramAccessor programAccessor, IVariableTranslationFactory factory)
        {
            this.programAccessor = programAccessor;
            equalityHintGenerator = new EqualityHintGenerator(factory);
        }

        public Tuple<string, IEnumerable<LemmaDecl>> GenerateTactic(Expr e)
        {
            var varCollector = new VariableCollector();
            varCollector.Visit(e);

            var lookupTyThms = new List<string>();
            var funMemThms = new List<string>();

            foreach (var v in varCollector.usedVars)
                try
                {
                    lookupTyThms.Add(programAccessor.LookupVarTyLemma(v));
                }
                catch
                {
                    //variable not found, possible if, for example, v is bound
                }

            var usedFuncs = functionCollector.UsedFunctions(e);
            foreach (var f in usedFuncs) funMemThms.Add(programAccessor.MembershipLemma(f));

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

            var tactic = ProofUtil.Apply(ProofUtil.MLTactic("typing_tac " + string.Join(" ", args), 1));

            return Tuple.Create(tactic, hintLemmas);
        }
    }
}