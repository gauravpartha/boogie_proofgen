using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Boogie;
using ProofGeneration.Isa;
using ProofGeneration.Util;

namespace ProofGeneration
{
    class BasicCmdIsaVisitor : ResultReadOnlyVisitor<Term>
    {

        //It's possible that the AST has two different variables which have the same name. Therefore we use an IsaUniqueNamer to 
        //avoid name clashes between different variables.
        private readonly IsaUniqueNamer uniqueNamer;
   
        public BasicCmdIsaVisitor(IsaUniqueNamer uniqueNamer)
        {
            this.uniqueNamer = uniqueNamer;
        }

        public BasicCmdIsaVisitor() : this(new IsaUniqueNamer()) { }
   
        [ContractInvariantMethod]
        void ObjectInvariant()
        {
            Contract.Invariant(Results != null);
            Contract.Invariant(Results.Count <= 1);
        }

        public IList<Term> Translate(IList<Cmd> cmds)
        {
            IList<Term> cmdsIsa = new List<Term>();

            foreach (Cmd cmd in cmds)
            {
                cmdsIsa.Add(Translate(cmd));
                if (!StateIsFresh())
                {
                    throw new IsaCFGGeneratorException(IsaCFGGeneratorException.Reason.VISITOR_NOT_FRESH);
                }
            }

            return cmdsIsa;
        }

        protected override bool TranslatePrecondition(Absy node)
        {
            return node is Cmd || node is Expr;
        }

        public override Cmd VisitAssertCmd(AssertCmd node)
        {
            Term result = Translate(node.Expr);
            ReturnResult(IsaBoogieTerm.Assert(result));

            return node;
        }

        public override Cmd VisitAssertEnsuresCmd(AssertEnsuresCmd node)
        {
            //ignore ensures node for now, TODO
            return VisitAssertCmd(node);
        }


        public override Cmd VisitAssertRequiresCmd(AssertRequiresCmd node)
        {
            //ignore requires node for now, TODO
            return VisitAssertCmd(node);
        }

        public override Cmd VisitAssumeCmd(AssumeCmd node)
        {
            Term result = Translate(node.Expr);
            ReturnResult(IsaBoogieTerm.Assume(result));

            return node;
        }

        public override Cmd VisitAssignCmd(AssignCmd node)
        {
            if ((node.Lhss.Count != node.Rhss.Count))
            {
                throw new ProofGenUnexpectedStateException(typeof(BasicCmdIsaVisitor), "different number of lhs and rhs");
            }

            var lhsResults = node.Lhss.Select(lhs => Translate(lhs)).ToList();
            var rhsResults = node.Rhss.Select(rhs => Translate(rhs)).ToList();

            IList<Term> results = new List<Term>();
            lhsResults.ZipDo(rhsResults, (lhs, rhs) => results.Add(new TermTuple(new List<Term>() { lhs, rhs })));

            ReturnResult(IsaBoogieTerm.Assign(lhsResults, rhsResults));
            return node;
        }

        public override AssignLhs VisitSimpleAssignLhs(SimpleAssignLhs node)
        {
            ReturnResult(new StringConst(GetStringFromIdentifierExpr(node.AssignedVariable)));
            return node;
        }

        public override Expr VisitNAryExpr(NAryExpr node)
        {
            IList<Term> args = new List<Term>();

            foreach(Expr expr in node.Args)
            {
                args.Add(Translate(expr));
            }

            IAppliableVisitor<Term> applicableIsaVisitor = new ApplicableIsaVisitor(args);
            Term res = node.Fun.Dispatch(applicableIsaVisitor);

            ReturnResult(res);
            return node;
        }

        //potential side effect
        public string GetStringFromIdentifierExpr(IdentifierExpr node)
        {
            return uniqueNamer.GetName(node.Decl, node.Name);
        }

        public override Expr VisitIdentifierExpr(IdentifierExpr node)
        {
            ReturnResult(IsaBoogieTerm.Var(GetStringFromIdentifierExpr(node)));
            //TODO: also look at decl?
            return node;
        }

        public override Expr VisitLiteralExpr(LiteralExpr node)
        {
            if (node.Type.IsBool)
            {
                ReturnResult(IsaBoogieTerm.ExprFromVal(IsaBoogieTerm.BoolVal(node.asBool)));
            } else if(node.Type.IsInt)
            {
                ReturnResult(IsaBoogieTerm.ExprFromVal(IsaBoogieTerm.IntVal(node.asBigNum)));
            }

            return node;
        }

        //not implemented cmds
        public override Cmd VisitHavocCmd(HavocCmd node)
        {
            //handled elsewhere, since havoc of multiple variables is desugared into multiple basic havoc commands
            throw new NotImplementedException();
        }
        public override Cmd VisitCallCmd(CallCmd node)
        {
            throw new NotImplementedException();
        }
        public override Cmd VisitParCallCmd(ParCallCmd node)
        {
            throw new NotImplementedException();
        }
        public override List<Cmd> VisitCmdSeq(List<Cmd> cmdSeq)
        {
            throw new NotImplementedException();
        }
        public override Choice VisitChoice(Choice node)
        {
            throw new NotImplementedException();
        }
        public override Cmd VisitCommentCmd(CommentCmd node)
        {
            throw new NotImplementedException();
        }
        public override Cmd VisitRE(RE node)
        {
            throw new NotImplementedException();
        }
        public override List<RE> VisitRESeq(List<RE> reSeq)
        {
            throw new NotImplementedException();
        }
        public override YieldCmd VisitYieldCmd(YieldCmd node)
        {
            throw new NotImplementedException();
        }


        //not implemented exprs
        public override Expr VisitBvConcatExpr(BvConcatExpr node)
        {
            throw new NotImplementedException();
        }
        public override Expr VisitCodeExpr(CodeExpr node)
        {
            throw new NotImplementedException();
        }
        public override Expr VisitExistsExpr(ExistsExpr node)
        {
            throw new NotImplementedException();
        }
        public override Expr VisitBvExtractExpr(BvExtractExpr node)
        {
            throw new NotImplementedException();
        }
        public override Expr VisitExpr(Expr node)
        {
            throw new NotImplementedException();
        }
        public override IList<Expr> VisitExprSeq(IList<Expr> exprSeq)
        {
            throw new NotImplementedException();
        }
        public override Expr VisitForallExpr(ForallExpr node)
        {
            throw new NotImplementedException();
        }
        public override Expr VisitLambdaExpr(LambdaExpr node)
        {
            throw new NotImplementedException();
        }
        public override Expr VisitLetExpr(LetExpr node)
        {
            throw new NotImplementedException();
        }
        public override Expr VisitOldExpr(OldExpr node)
        {
            throw new NotImplementedException();
        }
        public override BinderExpr VisitBinderExpr(BinderExpr node)
        {
            throw new NotImplementedException();
        }
        public override QuantifierExpr VisitQuantifierExpr(QuantifierExpr node)
        {
            throw new NotImplementedException();
        }

    }
}
