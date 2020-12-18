using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Boogie.ProofGen;
using Microsoft.Boogie.VCExprAST;
using ProofGeneration.Util;

namespace ProofGeneration.ProgramToVCProof
{
    public class AxiomHandler
    {
        public static IEnumerable<VCExpr> AxiomInfo(bool programIsPolymorphic, IEnumerable<Axiom> axioms,
            VCExpr vcAxioms, VCExpr typeAxioms, List<VCAxiomInfo> typeAxiomInfo,
            out List<VCAxiomInfo> allAxiomsInfo)
        {
            
            List<VCExpr> vcBoogieAxioms = DeconstructAxiomsNoChecks(vcAxioms).ToList();
            int nAxioms = axioms.Count();

            List<VCExpr> consideredVCBoogieAxioms;
            
            if (programIsPolymorphic)
            {
                if(vcBoogieAxioms.Count != nAxioms + 3 )
                    //+3, since we currently ignore the three type ordering axioms
                    throw new ProofGenUnexpectedStateException(typeof(ProofGenerationLayer),
                    "vc axioms not in-sync with Boogie axioms");

                consideredVCBoogieAxioms = vcBoogieAxioms.GetRange(3, nAxioms);
            }
            else
            {
                if (nAxioms == 0)  
                {
                    if(vcBoogieAxioms.Count != 1 || !vcBoogieAxioms.First().Equals(VCExpressionGenerator.True))
                        throw new ProofGenUnexpectedStateException(typeof(ProofGenerationLayer),
                            "no axioms and no polymorphism, but vc axioms are not (syntactically) equivalent to True");

                    consideredVCBoogieAxioms = new List<VCExpr>();
                }
                else
                {
                    if (vcBoogieAxioms.Count != nAxioms)
                    {
                        throw new ProofGenUnexpectedStateException(typeof(ProofGenerationLayer),
                            "no axioms and no polymorphism, but vc axioms are not (syntactically) equivalent to True");
                    }

                    consideredVCBoogieAxioms = new List<VCExpr>(vcBoogieAxioms);
                }
            }
            
            
            List<VCAxiomInfo> typeAxiomInfoPruned = new List<VCAxiomInfo>();
            List<VCExpr> vcTypeAxioms = new List<VCExpr>();
            if (programIsPolymorphic)
            {
                typeAxiomInfoPruned = typeAxiomInfo.Where(a => !a.Expr.Equals(VCExpressionGenerator.True)).ToList();
                vcTypeAxioms = DeconstructAxiomsNoChecks(typeAxioms).ToList();
                if (vcTypeAxioms.Count != typeAxiomInfoPruned.Count)
                {
                    throw new ProofGenUnexpectedStateException(typeof(ProofGenerationLayer),
                        "type axiom info not in-sync with actual type axioms");
                }
            }

            allAxiomsInfo = GetBoogieAxiomInfo(axioms, consideredVCBoogieAxioms).Union(typeAxiomInfoPruned).ToList();
            return consideredVCBoogieAxioms.Union(vcTypeAxioms);
        }

        private static IEnumerable<VCExpr> DeconstructAxiomsNoChecks(VCExpr vcAxioms)
        {
            var result = new List<VCExpr>();
            VCExpr vcAxiomsTemp = vcAxioms;
            while (vcAxiomsTemp is VCExprNAry vcNAry && vcNAry.Op == VCExpressionGenerator.AndOp && vcNAry.Length == 2)
            {
                result.Add(vcNAry[1]);
                vcAxiomsTemp = vcNAry[0];
            }
            result.Add(vcAxiomsTemp);
            result.Reverse();
            return result;
        }

        
        private static IEnumerable<VCExpr> DeconstructAxioms(IEnumerable<Axiom> axioms, VCExpr vcAxioms)
        {
            int numAxioms = axioms.Count();

            /* Simplifying assumption: vcAxioms of the form (((Ax1 /\ Ax2) /\ Ax3) /\ Ax4) /\ ...
             * This is not true in general due to simplifications made by Boogie such as True /\ True -> True
             * Also, I don't know yet how type axioms are handled. */
            var result = new List<VCExpr>();

            if (numAxioms > 1)
            {
                VCExpr vcAxiomsTemp = vcAxioms;
                while (vcAxiomsTemp is VCExprNAry vcNAry && vcNAry.Op == VCExpressionGenerator.AndOp && vcNAry.Length == 2)
                {
                    result.Add(vcNAry[1]);
                    vcAxiomsTemp = vcNAry[0];
                }
                result.Add(vcAxiomsTemp);
                if (result.Count != numAxioms)
                {
                    throw new ProofGenUnexpectedStateException(typeof(ProofGenerationLayer),
                        "Not supported: vcAxioms not in -sync with Boogie axioms(could be due to optimizations / type axioms)");
                }
                result.Reverse();
                return result;
            } else if(numAxioms == 1 || (numAxioms == 0 && vcAxioms.Equals(VCExpressionGenerator.True)))
            {
                return new List<VCExpr> { vcAxioms };
            } else 
            {
                throw new ProofGenUnexpectedStateException(typeof(ProofGenUnexpectedStateException),
                    "Not supported: vcAxioms not in-sync with Boogie axioms (could be due to optimizations/type axioms)");
            }
        }
        
        /// <summary>
        /// Get axiom information for those the user-defined axioms in the Boogie program.
        /// <paramref name="vcAxioms" /> may contain more than elements than <paramref name="axioms"/>, but the first
        /// n axioms should correspond to 
        /// </summary>
        private static List<VCAxiomInfo> GetBoogieAxiomInfo(IEnumerable<Axiom> axioms, List<VCExpr> vcAxioms)
        {
            var result = new List<VCAxiomInfo>();
            axioms.ZipDo(vcAxioms, (axiom, expr) =>
            {
               result.Add(new VcBoogieAxiomInfo(expr, axiom)); 
            });

            return result;
        }
    }
}