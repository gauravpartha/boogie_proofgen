using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface.VariableTranslation;
using ProofGeneration.Isa;

namespace ProofGeneration
{
    internal class BasicCmdIsaVisitor : ResultReadOnlyVisitor<Term>
    {
        private readonly BoogieVariableTranslation boogieVarTranslation;
        private readonly TypeIsaVisitor typeIsaVisitor;

        private readonly IVariableTranslationFactory variableFactory;


        public BasicCmdIsaVisitor(IVariableTranslationFactory variableFactory)
        {
            this.variableFactory = variableFactory;
            boogieVarTranslation = variableFactory.CreateTranslation();
            //by sharing TypeVarTranslation, changes in the bound variables will be visible in the type visitor
            typeIsaVisitor = new TypeIsaVisitor(boogieVarTranslation.TypeVarTranslation);
        }

        [ContractInvariantMethod]
        private void ObjectInvariant()
        {
            Contract.Invariant(Results != null);
            Contract.Invariant(Results.Count <= 1);
        }

        public IList<Term> Translate(IList<Cmd> cmds)
        {
            IList<Term> cmdsIsa = new List<Term>();

            foreach (var cmd in cmds)
            {
                cmdsIsa.Add(Translate(cmd));
                if (!StateIsFresh()) throw new ProofGenUnexpectedStateException(GetType(), "Visitor not fresh");
            }

            return cmdsIsa;
        }

        protected override bool TranslatePrecondition(Absy node)
        {
            return node is Cmd || node is Expr || node is AssignLhs;
        }

        public override Cmd VisitAssertCmd(AssertCmd node)
        {
            var result = Translate(node.Expr);
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
            var result = Translate(node.Expr);
            ReturnResult(IsaBoogieTerm.Assume(result));

            return node;
        }

        public override Cmd VisitAssignCmd(AssignCmd node)
        {
            if (node.Lhss.Count != node.Rhss.Count)
                throw new ProofGenUnexpectedStateException(typeof(BasicCmdIsaVisitor),
                    "different number of lhs and rhs");

            if (node.Lhss.Count != 1) throw new NotImplementedException("Parallel assignments are not supported.");

            /*
            var lhsResults = node.Lhss.Select(lhs => Translate(lhs)).ToList();
            var rhsResults = node.Rhss.Select(rhs => Translate(rhs)).ToList();
            IList<Term> results = new List<Term>();
            lhsResults.ZipDo(rhsResults, (lhs, rhs) => results.Add(new TermTuple(new List<Term>() { lhs, rhs })));
            */

            var lhs = Translate(node.Lhss[0]);
            var rhs = Translate(node.Rhss[0]);
            ReturnResult(IsaBoogieTerm.Assign(lhs, rhs));

            return node;
        }

        public override AssignLhs VisitSimpleAssignLhs(SimpleAssignLhs node)
        {
            if (boogieVarTranslation.VarTranslation.TryTranslateVariableId(node.AssignedVariable.Decl, out var varId,
                out _))
            {
                ReturnResult(varId);
                return node;
            }

            throw new ProofGenUnexpectedStateException(GetType(),
                "Cannot extract id from variable " + node.AssignedVariable.Name);
        }

        public override Expr VisitNAryExpr(NAryExpr node)
        {
            IList<Term> args = new List<Term>();

            foreach (var expr in node.Args) args.Add(Translate(expr));

            IAppliableVisitor<Term> applicableIsaVisitor =
                new ApplicableIsaVisitor(node.TypeParameters, args, boogieVarTranslation.TypeVarTranslation);
            var res = node.Fun.Dispatch(applicableIsaVisitor);

            ReturnResult(res);
            return node;
        }

        //potential side effect
        public Term GetIdFromIdentifierExpr(IdentifierExpr node)
        {
            if (boogieVarTranslation.VarTranslation.TryTranslateVariableId(node.Decl, out var varId, out _))
                return varId;

            throw new ProofGenUnexpectedStateException(GetType(), "Could not get id for variable " + node.Decl.Name);
            //TODO: check whether need unique name or not (under assumption that there are no variable name clashes, i.e., no shadowing)
            //return uniqueNamer.GetName(node.Decl, node.Name);
        }

        public override Expr VisitIdentifierExpr(IdentifierExpr node)
        {
            ReturnResult(boogieVarTranslation.VarTranslation.TranslateVariable(node.Decl, out _));
            return node;
        }

        public override Expr VisitLiteralExpr(LiteralExpr node)
        {
            ReturnResult(IsaBoogieTerm.ExprFromLiteral(IsaBoogieTerm.Literal(node)));
            return node;
        }

        public override QuantifierExpr VisitQuantifierExpr(QuantifierExpr node)
        {
            if (!(node is ForallExpr || node is ExistsExpr))
                throw new ProofGenUnexpectedStateException(GetType(), "can only handle forall and exists quantifiers");

            var isForall = IsForall(node);

            //Quantifers with multiple bound variables are desugared into multiple quantifiers expressions with single variables
            foreach (var boundVar in node.Dummies) boogieVarTranslation.VarTranslation.AddBoundVariable(boundVar);
            foreach (var boundTyVar in node.TypeParameters)
                boogieVarTranslation.TypeVarTranslation.AddBoundVariable(boundTyVar);

            var numValVarBefore = boogieVarTranslation.VarTranslation.NumBoundVariables();
            var numTyVarBefore = boogieVarTranslation.TypeVarTranslation.NumBoundVariables();

            var result = Translate(node.Body);

            if (numValVarBefore != boogieVarTranslation.VarTranslation.NumBoundVariables() ||
                numTyVarBefore != boogieVarTranslation.TypeVarTranslation.NumBoundVariables())
                throw new ProofGenUnexpectedStateException(GetType(),
                    "quantifier levels not the same before and after");

            for (var i = node.Dummies.Count - 1; i >= 0; i--)
            {
                boogieVarTranslation.VarTranslation.DropLastBoundVariable();
                var boundVar = node.Dummies[i];
                var boundVarType = typeIsaVisitor.Translate(boundVar.TypedIdent.Type);
                result = IsaBoogieTerm.Quantifier(isForall, boundVarType, result);
            }

            for (var i = node.TypeParameters.Count - 1; i >= 0; i--)
            {
                boogieVarTranslation.TypeVarTranslation.DropLastBoundVariable();
                result = IsaBoogieTerm.TypeQuantifier(isForall, result);
            }

            ReturnResult(result);
            return node;
        }

        private bool IsForall(QuantifierExpr quantifierExpr)
        {
            if (quantifierExpr is ForallExpr)
                return true;
            if (quantifierExpr is ExistsExpr)
                return false;
            throw new ProofGenUnexpectedStateException(GetType(), "Unexpected quantifier");
        }

        public override Expr VisitOldExpr(OldExpr node)
        {
            var body = Translate(node.Expr);
            ReturnResult(IsaBoogieTerm.Old(body));

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

        public override Expr VisitLambdaExpr(LambdaExpr node)
        {
            throw new NotImplementedException();
        }

        public override Expr VisitLetExpr(LetExpr node)
        {
            throw new NotImplementedException();
        }

        public override BinderExpr VisitBinderExpr(BinderExpr node)
        {
            throw new NotImplementedException();
        }
    }
}