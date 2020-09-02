using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Boogie.TypeErasure;
using Microsoft.Boogie.VCExprAST;

namespace ProofGeneration.VCProofGen
{
    class VCVarFunTranslator : IVCVarFunTranslator
    {
        private readonly IDictionary<VCExprVar, Variable> vcToBoogie;
        private readonly IDictionary<Variable, VCExprVar> boogieToVc;

        private readonly IDictionary<Function, Function> origToErasedFun;
        private readonly IDictionary<Function, Function> erasedToOrigFun;

        public VCVarFunTranslator(IEnumerable<Variable> vars, 
            IDictionary<Function, Function> origToErasedFun,
            Boogie2VCExprTranslator translator, 
            TypeAxiomBuilderPremisses axiomBuilder)
        {
            this.origToErasedFun = origToErasedFun;
            this.erasedToOrigFun = origToErasedFun.ToDictionary((i) => i.Value, (i) => i.Key);

            boogieToVc = new Dictionary<Variable, VCExprVar>();
            vcToBoogie = new Dictionary<VCExprVar, Variable>();
            foreach (var v in vars)
            {
                VCExprVar result = translator.TryLookupVariable(v);
                if (result != null)
                {
                    if (axiomBuilder != null)
                    {
                        result = axiomBuilder.TryTyped2Untyped(result);
                        if (result == null)
                            throw new ProofGenUnexpectedStateException(typeof(VCToIsaInterface), "Cannot retrieve untyped VCExprVar");
                    }

                    vcToBoogie.Add(result, v);
                    boogieToVc.Add(v, result);
                }
            }
        }

        public bool TranslateBoogieVar(Variable v, out VCExprVar result)
        {
            if(boogieToVc.TryGetValue(v, out VCExprVar resultInternal))
            {
                result = resultInternal;
                return true; 
            } else
            {
                result = null;
                return false;
            }
        }

        public bool TranslateVCVar(VCExprVar v, out Variable result)
        {
            if(vcToBoogie.TryGetValue(v, out Variable resultInternal)) {
                result = resultInternal;
                return true;
            } else
            {
                result = null;
                return false;
            }
        }

        public bool TranslateBoogieFunction(Function v, out Function result)
        {
            if (origToErasedFun.TryGetValue(v, out Function internalResult))
            {
                result = internalResult;
                return true;
            }
            else
            {
                result = null;
                return false;
            }
        }

        public bool TranslateVCFunction(Function vcFun, out Function result)
        {
            if (erasedToOrigFun.TryGetValue(vcFun, out Function internalResult))
            {
                result = internalResult;
                return true;
            }
            else
            {
                result = null;
                return false;
            }
        }
    }
}
