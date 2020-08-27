using System.Collections.Generic;
using Microsoft.Boogie;
using Microsoft.Boogie.TypeErasure;
using Microsoft.Boogie.VCExprAST;

namespace ProofGeneration.VCProofGen
{
    class VCVarTranslator : IVCVarTranslator
    {
        private readonly IDictionary<VCExprVar, Variable> vcToBoogie;
        private readonly IDictionary<Variable, VCExprVar> boogieToVc;

        public VCVarTranslator(IEnumerable<Variable> vars, Boogie2VCExprTranslator translator, TypeAxiomBuilderPremisses axiomBuilder)
        {
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
    }
}
