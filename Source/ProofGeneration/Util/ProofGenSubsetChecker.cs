using System;
using System.Linq;
using System.Transactions;
using Isabelle.Ast;
using Microsoft.Boogie;
using Type = Microsoft.Boogie.Type;

namespace ProofGeneration.Util
{
    /// <summary>
    /// Checks in a whether the input program is potentially supported by proof generation.
    /// </summary>
    public class ProofGenSubsetChecker : ResultReadOnlyVisitor<Term>
    {
        private object problematicNode;
        private bool result;

        protected override bool TranslatePrecondition(Absy node)
        {
            return true;
        }

        /// <summary>
        /// If false is returned, then the input is not supported.
        /// If true is returned, then the input is potentially supported.
        /// </summary>
        public bool ProofGenPotentiallySupportsSubset(Program p, out object resultNode)
        {
            problematicNode = null;
            Visit(p);
            resultNode = problematicNode;
            return problematicNode == null;
        }

        public override Procedure VisitProcedure(Procedure node)
        {
            //no procedure type parameters, free pre- and postconditions, no where clauses
            if (node.TypeParameters.Any() || 
                node.Requires.Any(req => req.Free) || 
                node.Ensures.Any(ens => ens.Free) ||
                node.InParams.Union(node.OutParams).Any(v => v.TypedIdent.WhereExpr != null))
            {
                problematicNode = node;
                return node;
            }

            return base.VisitProcedure(node);
        }

        public override Implementation VisitImplementation(Implementation node)
        {
            //no where clauses
            if (node.LocVars.Any(v => v.TypedIdent.WhereExpr != null))
            {
                problematicNode = node;
                return node;
            }

            return base.VisitImplementation(node);
        }

        public override Type VisitBasicType(BasicType node)
        {
            //only support integers and booleans as basic types
            if (node.IsReal || node.isFloat || node.IsBv || node.IsString || node.IsRMode || node.IsRegEx)
            {
                problematicNode = node;
                return node;
            }

            return base.VisitBasicType(node);
        }
        
        public override Type VisitFloatType(FloatType node)
        {
            problematicNode = node;
            return node;
        }

        #region regex
        //do not support regular expressions
        public override Sequential VisitSequential(Sequential node)
        {
            problematicNode = node;
            return node;
        }

        public override Choice VisitChoice(Choice node)
        {
            problematicNode = node;
            return node;
        }
        
        public override Cmd VisitRE(RE node)
        {
            problematicNode = node;
            return node;
        }
        
        public override AtomicRE VisitAtomicRE(AtomicRE node)
        {
            problematicNode = node;
            return node;
        }
        #endregion

        
        //do not support code block expressions
        public override Expr VisitCodeExpr(CodeExpr node)
        {
            problematicNode = node;
            return node;
        }

        #region maps 
        
        //do not support maps
        public override Expr VisitLambdaExpr(LambdaExpr node)
        {
            problematicNode = node;
            return node;
        }

        public override MapType VisitMapType(MapType node)
        {
            problematicNode = node;
            return node;
        }

        public override AssignLhs VisitMapAssignLhs(MapAssignLhs node)
        {
            problematicNode = node;
            return node;
        }

        public override Type VisitMapTypeProxy(MapTypeProxy node)
        {
            problematicNode = node;
            return node;
        }
        #endregion
        
        #region bitvectors
        
        //do not support bitvectors
        public override Type VisitBvType(BvType node)
        {
            problematicNode = node;
            return node;
        }
        
        public override Expr VisitBvConcatExpr(BvConcatExpr node)
        {
            problematicNode = node;
            return node;
        }

        public override Expr VisitBvExtractExpr(BvExtractExpr node)
        {
            problematicNode = node;
            return node;
        }

        public override Type VisitBvTypeProxy(BvTypeProxy node)
        {
            problematicNode = node;
            return node;
        }
        #endregion
        
        #region civl
        
        //do not support concurrent intermediate verification language (CIVL) features
        public override YieldCmd VisitYieldCmd(YieldCmd node)
        {
            problematicNode = node;
            return node;
        }
        
        public override Cmd VisitParCallCmd(ParCallCmd node)
        {
            problematicNode = node;
            return node;
        }
        #endregion
    }
}