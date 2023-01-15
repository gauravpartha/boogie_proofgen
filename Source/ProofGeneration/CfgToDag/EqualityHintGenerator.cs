using System;
using System.Collections.Generic;
using System.Linq;
using Isabelle.Ast;
using Isabelle.ML;
using Isabelle.Util;
using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface.VariableTranslation;
using ProofGeneration.Util;
using Type = Microsoft.Boogie.Type;

#nullable enable
namespace ProofGeneration.CfgToDag
{
    public class EqualityHintGenerator : ResultReadOnlyVisitor<string?>
    {
        private readonly IVariableTranslationFactory variableFactory;
        private IList<LemmaDecl> _hintLemmas;

        private int count;
        private IVariableTranslation<TypeVariable> tyVarTranslation;

        public EqualityHintGenerator(IVariableTranslationFactory variableFactory)
        {
            this.variableFactory = variableFactory;
        }

        public override string? Translate(Absy node)
        {
            if (!StateIsFresh()) throw new ProofGenUnexpectedStateException(GetType());
            Visit(node);

            return !Results.TryPop(out string? result) ? null : result;
        }

        protected override bool TranslatePrecondition(Absy node)
        {
            return true;
        }

        public Tuple<IEnumerable<LemmaDecl>, string> GetHints(Expr e)
        {
            _hintLemmas = new List<LemmaDecl>();
            tyVarTranslation = variableFactory.CreateTranslation().TypeVarTranslation;
            Visit(e);

            if (!Results.TryPop(out string? hintMLString) || hintMLString == null)
            {
              hintMLString = "NoPolyHint";
            }

            return Tuple.Create<IEnumerable<LemmaDecl>, string>(_hintLemmas, hintMLString);
        }

        public override Trigger VisitTrigger(Trigger node)
        {
          //ignore triggers
          return node;
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
            string? curHint = null;
            
            
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
              {
                curHint = AddHint(unifier);
              }
              else
              {
                throw new ProofGenUnexpectedStateException("Cannot unify types for equality");
              }
            }

            var childrenHints = new List<string>();
            bool hintsTrivial = curHint == null;

            for (int i = 0, n = node.Args.Count; i < n; i++)
            {
              string? childHint = Translate(cce.NonNull(node.Args[i]));
              if (childHint == null)
              {
                childrenHints.Add("NoPolyHint");
              }
              else
              {
                hintsTrivial = false;
                childrenHints.Add(childHint);
              }
            }

            if (hintsTrivial)
            {
              ReturnResult(null);
            }
            else
            {
              var curHintString = curHint == null ? MLUtil.MLNone() : MLUtil.MLSome(MLUtil.IsaToMLThm(curHint));
              ReturnResult("(PolyHintNode " + MLUtil.MLTuple(curHintString, MLUtil.MLList(childrenHints)) + ")");
            }

            return node;
        }

        private string? AddHint(IDictionary<TypeVariable, Type> unifier)
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

            if (subst.Any())
            {
              var nextHintLemma =
                  new LemmaDecl(getNextHintName(), ContextElem.CreateEmptyContext(),
                      new TermApp(IsaCommonTerms.TermIdentFromName("hint_ty_subst"), new TermList(subst)),
                      new Proof(new List<string> {ProofUtil.By("simp add: hint_ty_subst_def")})
                  );
              
              _hintLemmas.Add(nextHintLemma);

              return nextHintLemma.Name;
            }

            return null; //no hints needed if substitution is empty
        }

        private string getNextHintName()
        {
            count++;
            return "ty_hint_" + count;
        }
    }
}