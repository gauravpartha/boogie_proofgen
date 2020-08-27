using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.BoogieIsaInterface.VariableTranslation;
using ProofGeneration.Isa;
using ProofGeneration.Util;

namespace ProofGeneration
{
    class BasicCmdIsaVisitor : ResultReadOnlyVisitor<Term>
    {

        //It's possible that the AST has two different variables which have the same name. Therefore we use an IsaUniqueNamer to 
        //avoid name clashes between different variables.
        //UPDATE (20.07.2020): do not support shadowing, so for now we don't rename
        private readonly IsaUniqueNamer uniqueNamer;

        private readonly BoogieVariableTranslation boogieVarTranslation;
        private readonly TypeIsaVisitor typeIsaVisitor;

        private readonly IVariableTranslationFactory variableFactory;


        public BasicCmdIsaVisitor(IsaUniqueNamer uniqueNamer, IVariableTranslationFactory variableFactory)
        {
            this.variableFactory = variableFactory;
            boogieVarTranslation = variableFactory.CreateTranslation();
            //by sharing TypeVarTranslation, changes in the bound variables will be visible in the type visitor
            this.typeIsaVisitor = new TypeIsaVisitor(boogieVarTranslation.TypeVarTranslation);
            this.uniqueNamer = uniqueNamer;
        }

        public BasicCmdIsaVisitor(IVariableTranslationFactory variableFactory) : this(new IsaUniqueNamer(), variableFactory)
        { }
   
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
            return node is Cmd || node is Expr || node is AssignLhs;
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

            IAppliableVisitor<Term> applicableIsaVisitor = 
                new ApplicableIsaVisitor(node.TypeParameters, args, boogieVarTranslation.TypeVarTranslation);
            Term res = node.Fun.Dispatch(applicableIsaVisitor);

            ReturnResult(res);
            return node;
        }

        //potential side effect
        public string GetStringFromIdentifierExpr(IdentifierExpr node)
        {
            return node.Name;
            //TODO: check whether need unique name or not (under assumption that there are no variable name clashes, i.e., no shadowing)
            //return uniqueNamer.GetName(node.Decl, node.Name);
        }

        public override Expr VisitIdentifierExpr(IdentifierExpr node)
        {
            ReturnResult(IsaBoogieTerm.Var(boogieVarTranslation.VarTranslation.TranslateVariable(node.Decl)));            
            return node;
        }

        public override Expr VisitLiteralExpr(LiteralExpr node)
        {
            ReturnResult(IsaBoogieTerm.ExprFromVal(IsaBoogieTerm.ValFromLiteral(node)));
            return node;
        }

        public override QuantifierExpr VisitQuantifierExpr(QuantifierExpr node)
        {
            if(!(node is ForallExpr || node is ExistsExpr))
            {
                throw new ProofGenUnexpectedStateException(GetType(), "can only handle forall and exists quantifiers");
            }

            bool isForall = IsForall(node);

            //Quantifers with multiple bound variables are desugared into multiple quantifiers expressions with single variables
            foreach(Variable boundVar in node.Dummies)
            {
                boogieVarTranslation.VarTranslation.AddBoundVariable(boundVar);
            }
            foreach(TypeVariable boundTyVar in node.TypeParameters)
            {
                boogieVarTranslation.TypeVarTranslation.AddBoundVariable(boundTyVar);
            }

            int numValVarBefore = boogieVarTranslation.VarTranslation.NumBoundVariables();
            int numTyVarBefore = boogieVarTranslation.TypeVarTranslation.NumBoundVariables();

            Term result = Translate(node.Body);

            if (numValVarBefore != boogieVarTranslation.VarTranslation.NumBoundVariables() || 
                numTyVarBefore != boogieVarTranslation.TypeVarTranslation.NumBoundVariables())
            {
                throw new ProofGenUnexpectedStateException(GetType(), "quantifier levels not the same before and after");
            }

            for(int i = node.Dummies.Count-1; i >= 0; i--)
            {
                boogieVarTranslation.VarTranslation.DropLastBoundVariable();
                Variable boundVar = node.Dummies[i];
                Term boundVarType = typeIsaVisitor.Translate(boundVar.TypedIdent.Type);
                result = IsaBoogieTerm.Quantifier(isForall, boundVarType, result);
            }

            for(int i = node.TypeParameters.Count-1; i >= 0; i--)
            {
                boogieVarTranslation.TypeVarTranslation.DropLastBoundVariable();
                TypeVariable boundTyVar = node.TypeParameters[i];
                result = IsaBoogieTerm.TypeQuantifier(isForall, result);
            }

            ReturnResult(result);
            return node;
        }

        private bool IsForall(QuantifierExpr quantifierExpr)
        {
            if(quantifierExpr is ForallExpr)
            {
                return true;
            } else if(quantifierExpr is ExistsExpr)
            {
                return false;
            } else
            {
                throw new ProofGenUnexpectedStateException(GetType(), "Unexpected quantifier");
            }
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
        public override Expr VisitOldExpr(OldExpr node)
        {
            throw new NotImplementedException();
        }
        public override BinderExpr VisitBinderExpr(BinderExpr node)
        {
            throw new NotImplementedException();
        }

    }
}
