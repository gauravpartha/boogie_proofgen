using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using Microsoft.Basetypes;
using Microsoft.Boogie;


namespace ProofGeneration
{
    class BasicCmdIsaVisitor : ResultReadOnlyVisitor<Term>
    {

        [ContractInvariantMethod]
        void ObjectInvariant()
        {
            Contract.Invariant(Results != null);
            Contract.Invariant(Results.Count <= 1);
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

        public override Cmd VisitAssumeCmd(AssumeCmd node)
        {
            Term result = Translate(node.Expr);
            ReturnResult(IsaBoogieTerm.Assume(result));

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

        public override Expr VisitIdentifierExpr(IdentifierExpr node)
        {
            ReturnResult(IsaBoogieTerm.Var(node.Name));
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

    }
}
