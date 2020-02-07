using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace ProofGeneration.VCProofGen
{
    /**
     * Removes labels from verification conditions such that one obtains a verification condition 
     * that is valid if and only if the original verification is valid.
     **/
    public class VCExprLabelRemover : MutatingVCExprVisitor<bool>
    {
        public VCExprLabelRemover(VCExpressionGenerator gen) : base(gen)
        {
            
        }
        
        public static VCExpr RemoveLabels(VCExpr expr, VCExpressionGenerator gen)
        {
            return new VCExprLabelRemover(gen).Mutate(expr, true);
        }
        
        protected override VCExpr/*!*/ UpdateModifiedNode(VCExprNAry/*!*/ originalNode,
                                              List<VCExpr/*!*/>/*!*/ newSubExprs,
                                              bool changed,
                                              bool arg)
        {
            if((originalNode.Op is VCExprLabelOp originalLabel) && !originalLabel.pos)
            {
                //corresponds to an assertion, ignore label and directly return associated assertion
                Contract.Assert(newSubExprs.Count == 1);
                return newSubExprs.First();
            } else if (originalNode.Op.Equals(VCExpressionGenerator.ImpliesOp))
            {
                Contract.Assert(newSubExprs.Count == 2);
                if (newSubExprs[0] is VCExprNAry leftNAry)
                {
                    if (leftNAry.Op is VCExprLabelOp label)
                    {
                        //should be a positive label
                        Contract.Assert(label.pos);
                        //ignore label and directly return the right hand side
                        return newSubExprs[1];
                    }
                }
            }
            
            if (changed)
                return Gen.Function(originalNode.Op,
                                   newSubExprs, originalNode.TypeArguments);
            else
                return originalNode;
        }

    }

}
