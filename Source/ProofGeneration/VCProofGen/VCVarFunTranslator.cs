using System.Collections.Generic;
using Microsoft.Boogie;
using Microsoft.Boogie.TypeErasure;
using Microsoft.Boogie.VCExprAST;
using ProofGeneration.Util;

namespace ProofGeneration.VCProofGen
{
    internal class VCVarFunTranslator : IVCVarFunTranslator
    {
        private readonly IDictionary<Variable, VCExprVar> boogieToVc;
        private readonly IDictionary<Function, Function> erasedToOrigFun;

        private readonly IDictionary<Function, Function> origToErasedFun;
        private readonly IDictionary<VCExprVar, Variable> vcToBoogie;

        public VCVarFunTranslator(IEnumerable<Variable> vars,
            IDictionary<Function, Function> origToErasedFun,
            Boogie2VCExprTranslator translator,
            TypeAxiomBuilderPremisses axiomBuilder)
        {
            this.origToErasedFun = origToErasedFun;
            erasedToOrigFun = origToErasedFun.InverseDict();

            boogieToVc = new Dictionary<Variable, VCExprVar>();
            vcToBoogie = new Dictionary<VCExprVar, Variable>();
            foreach (var v in vars)
            {
                var result = translator.TryLookupVariable(v);
                if (result != null)
                {
                    if (axiomBuilder != null)
                    {
                        result = axiomBuilder.TryTyped2Untyped(result);
                        if (result == null)
                        {
                            continue;
                        }
                    }

                    vcToBoogie.Add(result, v);
                    boogieToVc.Add(v, result);
                }
            }
        }

        public bool TranslateBoogieVar(Variable v, out VCExprVar result)
        {
            if (boogieToVc.TryGetValue(v, out var resultInternal))
            {
                result = resultInternal;
                return true;
            }

            result = null;
            return false;
        }

        public bool TranslateVCVar(VCExprVar v, out Variable result)
        {
            if (vcToBoogie.TryGetValue(v, out var resultInternal))
            {
                result = resultInternal;
                return true;
            }

            result = null;
            return false;
        }

        public bool TranslateBoogieFunction(Function v, out Function result)
        {
            if (origToErasedFun.TryGetValue(v, out var internalResult))
            {
                result = internalResult;
                return true;
            }

            result = null;
            return false;
        }

        public bool TranslateVCFunction(Function vcFun, out Function result)
        {
            if (erasedToOrigFun.TryGetValue(vcFun, out var internalResult))
            {
                result = internalResult;
                return true;
            }

            result = null;
            return false;
        }
    }
}