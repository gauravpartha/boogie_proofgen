using System;
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
        public static IEnumerable<VCExpr> AxiomInfo(bool programIsPolymorphic, IEnumerable<Constant> uniqueConsts, IEnumerable<Axiom> axioms,
          VCExpr vcAxioms, VCExpr typeAxioms, List<VCAxiomInfo> typeAxiomInfo,
          out List<VCAxiomInfo> allAxiomsInfo)
        {
          var vcBoogieAxioms = DeconstructAxiomsNoChecks(vcAxioms).ToList();
          var nAxioms = axioms.Count();
          
          //there is one axiom for each subset S of unique constants with the same type if S has at least two elements
          int nConstDistinctAxioms =
            //uniqueConsts.GroupBy(e => e.TypedIdent.Type).Count(g => Enumerable.Count<Constant>(g) > 1);
            uniqueConsts.Count() > 1 ? 1 : 0;

          List<VCExpr> consideredVCBoogieAxioms;

          if (programIsPolymorphic)
          {
            if (vcBoogieAxioms.Count() == 1 && nAxioms == 0 &&
                vcBoogieAxioms.First().Equals(VCExpressionGenerator.True))
            {
              consideredVCBoogieAxioms = new List<VCExpr>();
            }
            else
            {
              if (vcBoogieAxioms.Count != nAxioms+nConstDistinctAxioms)
                //+3, since we currently ignore the three type ordering axioms
                throw new ProofGenUnexpectedStateException(typeof(ProofGenerationLayer),
                  "vc axioms not in-sync with Boogie axioms");

              consideredVCBoogieAxioms = vcBoogieAxioms.GetRange(0, nAxioms+nConstDistinctAxioms);
            }
          }
          else
          {
            if (nAxioms + nConstDistinctAxioms == 0)
            {
              if (vcBoogieAxioms.Count != 1 || !vcBoogieAxioms.First().Equals(VCExpressionGenerator.True))
                throw new ProofGenUnexpectedStateException(typeof(ProofGenerationLayer),
                  "no axioms and no polymorphism, but vc axioms are not (syntactically) equivalent to True");

              consideredVCBoogieAxioms = new List<VCExpr>();
            }
            else
            {
              if (vcBoogieAxioms.Count != nAxioms + nConstDistinctAxioms)
                throw new ProofGenUnexpectedStateException(typeof(ProofGenerationLayer),
                  "no axioms and no polymorphism, but vc axioms are not (syntactically) equivalent to True");

              consideredVCBoogieAxioms = new List<VCExpr>(vcBoogieAxioms);
            }
          }


          var typeAxiomInfoPruned = new List<VCAxiomInfo>();
          var vcTypeAxioms = new List<VCExpr>();
          if (programIsPolymorphic)
          {
            typeAxiomInfoPruned = typeAxiomInfo.Where(a => !a.Expr.Equals(VCExpressionGenerator.True)).ToList();
            vcTypeAxioms = DeconstructAxiomsNoChecks(typeAxioms).ToList();
            if (vcTypeAxioms.Count != typeAxiomInfoPruned.Count)
              throw new ProofGenUnexpectedStateException(typeof(ProofGenerationLayer),
                "type axiom info not in-sync with actual type axioms");
          }

          //TODO: make sure code that relies on axioms being unique still work (maps that take axioms as keys can be problematic)
          //don't use union, otherwise duplicates will be pruned, but want to keep each one
          IEnumerable<Axiom> reorderedBoogieAxioms = GetReorderedDeclarations(axioms);
          allAxiomsInfo = GetBoogieAxiomInfo(reorderedBoogieAxioms, consideredVCBoogieAxioms).Concat(typeAxiomInfoPruned).ToList();
          return consideredVCBoogieAxioms.Concat(vcTypeAxioms);
        }

        private static IEnumerable<VCExpr> DeconstructAxiomsNoChecks(VCExpr vcAxioms)
        {
            var result = new List<VCExpr>();
            var vcAxiomsTemp = vcAxioms;
            while (vcAxiomsTemp is VCExprNAry vcNAry && vcNAry.Op == VCExpressionGenerator.AndOp && vcNAry.Length == 2)
            {
                result.Add(vcNAry[1]);
                vcAxiomsTemp = vcNAry[0];
            }

            result.Add(vcAxiomsTemp);
            result.Reverse();
            return result;
        }
      
        //Copied from Checker.cs. TODO: find better way of getting reordered declarations
        private static IEnumerable<Axiom> GetReorderedDeclarations(IEnumerable<Axiom> declarations)
        {
          var seed = CommandLineOptions.Clo.RandomSeed;
          var random = seed != null ? new Random(seed.Value) : null;
          return GetReorderedDeclarations(declarations, random);
        }
      
        private static IEnumerable<Axiom> GetReorderedDeclarations(IEnumerable<Axiom> declarations, Random random)
        {
          if (random == null) {
            // By ordering the declarations based on their content and naming them based on order, the solver input stays content under reordering and renaming.
            return CommandLineOptions.Clo.NormalizeDeclarationOrder
              ? declarations.OrderBy(d => d.ContentHash)
              : declarations;
          }
          var copy = declarations.ToList();
          Microsoft.Boogie.Util.Shuffle(random, copy);
          return copy;
        }

        private static IEnumerable<VCExpr> DeconstructAxioms(IEnumerable<Axiom> axioms, VCExpr vcAxioms)
        {
            var numAxioms = axioms.Count();

            /* Simplifying assumption: vcAxioms of the form (((Ax1 /\ Ax2) /\ Ax3) /\ Ax4) /\ ...
             * This is not true in general due to simplifications made by Boogie such as True /\ True -> True
             * Also, I don't know yet how type axioms are handled. */
            var result = new List<VCExpr>();

            if (numAxioms > 1)
            {
                var vcAxiomsTemp = vcAxioms;
                while (vcAxiomsTemp is VCExprNAry vcNAry && vcNAry.Op == VCExpressionGenerator.AndOp &&
                       vcNAry.Length == 2)
                {
                    result.Add(vcNAry[1]);
                    vcAxiomsTemp = vcNAry[0];
                }

                result.Add(vcAxiomsTemp);
                if (result.Count != numAxioms)
                    throw new ProofGenUnexpectedStateException(typeof(ProofGenerationLayer),
                        "Not supported: vcAxioms not in -sync with Boogie axioms(could be due to optimizations / type axioms)");
                result.Reverse();
                return result;
            }

            if (numAxioms == 1 || numAxioms == 0 && vcAxioms.Equals(VCExpressionGenerator.True))
                return new List<VCExpr> {vcAxioms};
            throw new ProofGenUnexpectedStateException(typeof(ProofGenUnexpectedStateException),
                "Not supported: vcAxioms not in-sync with Boogie axioms (could be due to optimizations/type axioms)");
        }

        /// <summary>
        ///     Get axiom information for those the user-defined axioms in the Boogie program.
        ///     <paramref name="vcAxioms" /> may contain more than elements than <paramref name="axioms" />, but the first
        ///     n axioms should correspond to
        /// </summary>
        private static List<VCAxiomInfo> GetBoogieAxiomInfo(IEnumerable<Axiom> axioms, List<VCExpr> vcAxioms)
        {
            var result = new List<VCAxiomInfo>();
            axioms.ZipDo(vcAxioms, (axiom, expr) => { result.Add(new VcBoogieAxiomInfo(expr, axiom)); });

            return result;
        }
    }
}