﻿using System.Collections.Generic;
using System.Linq;
using Isabelle.Ast;
using Isabelle.Util;
using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface.VariableTranslation;
using ProofGeneration.Util;

namespace ProofGeneration.CfgToDag
{
    public class EqualityHintGenerator : ResultReadOnlyVisitor<bool>
    {
        private readonly IVariableTranslationFactory variableFactory;
        private List<LemmaDecl> _hintLemmas;

        private int count;
        private IVariableTranslation<TypeVariable> tyVarTranslation;

        public EqualityHintGenerator(IVariableTranslationFactory variableFactory)
        {
            this.variableFactory = variableFactory;
        }

        protected override bool TranslatePrecondition(Absy node)
        {
            return true;
        }

        public IEnumerable<LemmaDecl> GetHints(Expr e)
        {
            _hintLemmas = new List<LemmaDecl>();
            tyVarTranslation = variableFactory.CreateTranslation().TypeVarTranslation;
            Visit(e);
            return _hintLemmas;
        }

        // need to push bound type variables
        public override QuantifierExpr VisitQuantifierExpr(QuantifierExpr node)
        {
            if (!(node is ForallExpr || node is ExistsExpr))
                throw new ProofGenUnexpectedStateException(GetType(), "can only handle forall and exists quantifiers");

            //Quantifers with multiple bound variables are desugared into multiple quantifiers expressions with single variables
            foreach (var boundTyVar in node.TypeParameters) tyVarTranslation.AddBoundVariable(boundTyVar);

            var numTyVarBefore = tyVarTranslation.NumBoundVariables();

            Visit(node.Body);

            if (numTyVarBefore != tyVarTranslation.NumBoundVariables())
                throw new ProofGenUnexpectedStateException(GetType(),
                    "quantifier levels not the same before and after");

            for (var i = node.TypeParameters.Count - 1; i >= 0; i--) tyVarTranslation.DropLastBoundVariable();

            return node;
        }

        public override Expr VisitNAryExpr(NAryExpr node)
        {
            if (node.Fun is BinaryOperator bop &&
                (bop.Op == BinaryOperator.Opcode.Eq || bop.Op == BinaryOperator.Opcode.Neq))
            {
                var leftTy = node.Args[0].Type;
                var rightTy = node.Args[1].Type;

                var /*!*/
                    unifiable = new List<TypeVariable>();
                unifiable.AddRange(leftTy.FreeVariables);
                unifiable.AddRange(rightTy.FreeVariables);
                var unifier = new Dictionary<TypeVariable /*!*/, Type /*!*/>();
                if (leftTy.Unify(rightTy, unifiable, unifier))
                    AddHint(unifier);
                else
                    throw new ProofGenUnexpectedStateException("Cannot unify types for equality");
            }

            return base.VisitNAryExpr(node);
        }

        private void AddHint(IDictionary<TypeVariable, Type> unifier)
        {
            var typeIsaVisitor = new TypeIsaVisitor(tyVarTranslation);
            IDictionary<int, Term> indexToType = new Dictionary<int, Term>();

            foreach (var entry in unifier)
                if (tyVarTranslation.TryTranslateVariableId(entry.Key, out var idTerm, out _) &&
                    idTerm is NatConst idNat)
                    indexToType.Add(idNat.Val, typeIsaVisitor.Translate(entry.Value));
                else
                    throw new ProofGenUnexpectedStateException("cannot retrieve id from type variable");

            var subst = new List<Term>();

            if (unifier.Any())
            {
                //not all type variables may be mapped 
                var maxKey = indexToType.Keys.Max();
                for (var i = 0; i <= maxKey; i++)
                    if (indexToType.TryGetValue(i, out var type))
                        subst.Add(type);
                    else
                        //need to fill, just add int type
                        subst.Add(IsaBoogieType.IntType());
            }

            var nextHintLemma =
                new LemmaDecl(getNextHintName(), ContextElem.CreateEmptyContext(),
                    new TermApp(IsaCommonTerms.TermIdentFromName("hint_ty_subst"), new TermList(subst)),
                    new Proof(new List<string> {ProofUtil.By("simp add: hint_ty_subst_def")})
                );
            _hintLemmas.Add(nextHintLemma);
        }

        private string getNextHintName()
        {
            count++;
            return "ty_hint_" + count;
        }
    }
}