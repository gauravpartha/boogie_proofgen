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

    }
}
