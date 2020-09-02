using System.Collections;
using Microsoft.Boogie;
using ProofGeneration.Isa;
using ProofGeneration.Util;
using ProofGeneration.VCProofGen;
using System.Collections.Generic;
using System.Linq;
using System.Diagnostics.Contracts;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.BoogieIsaInterface.VariableTranslation;

namespace ProofGeneration.ProgramToVCProof
{
    static class LemmaHelper
    {
        private static PureToBoogieValConverter pureToBoogieValConverter = new PureToBoogieValConverter();

        public static bool FinalStateIsMagic(Block block)
        {
            return
                block.Cmds.Any(cmd =>
                {
                    return cmd != null && cmd is PredicateCmd predCmd && predCmd.Expr is LiteralExpr predCond && predCond != null && predCond.IsFalse;
                });
        }

        public static Term ConjunctionOfSuccessorBlocks(IEnumerable<Block> successorBlocks, IDictionary<NamedDeclaration, Term> declToVCMapping, VCInstantiation<Block> vcinst)
        {
            return
            successorBlocks.
                Select(b_suc => vcinst.GetVCObjInstantiation(b_suc, declToVCMapping)).
                Aggregate((vc1, vc2) => new TermBinary(vc1, vc2, TermBinary.BinaryOpCode.AND));
        }

        public static Term BinaryOpAggregate(IEnumerable<Term> term, TermBinary.BinaryOpCode bop)
        {
            return term.Aggregate((arg, res) => new TermBinary(arg, res, bop));
        }

        public static IList<Term> VariableAssumptions(
            IEnumerable<Variable> programVars,
            Term state,
            IDictionary<NamedDeclaration, Term> declToVCMapping,
            IVariableTranslation<Variable> varTranslation)
        {
            var result = new List<Term>();
            foreach (Variable v in programVars)
            {
                result.Add(VariableAssumption(v, state, declToVCMapping[v], varTranslation));
            }

            return result;
        }

        public static Term VariableAssumption(Variable v, Term state, Term vcVar, IVariableTranslation<Variable> varTranslation)
        {
            if (varTranslation.TryTranslateVariableId(v, out Term varId))
            {
                Term left = new TermApp(state, varId);
                Term right =
                    IsaCommonTerms.SomeOption(pureToBoogieValConverter.ConvertToBoogieVal(v.TypedIdent.Type, vcVar));
                return new TermBinary(left, right, TermBinary.BinaryOpCode.EQ);
            }
            else
            {
                throw new ProofGenUnexpectedStateException(typeof(LemmaHelper), "Can't retrieve variable id");
            }
        }

        public static Term VariableAssumptionExplicit(Variable v, Term state, Term rhs, IsaUniqueNamer uniqueNamer)
        {
            Term left = new TermApp(state, new StringConst(v.Name));
            return new TermBinary(left, rhs, TermBinary.BinaryOpCode.EQ);
        }

        public static Term VariableTypeAssumption(Variable v, Term varContext, TypeIsaVisitor typeIsaVisitor)
        {
            Term left = new TermApp(varContext, new StringConst(v.Name));
            Term right = IsaCommonTerms.SomeOption(typeIsaVisitor.Translate(v.TypedIdent.Type));
            return new TermBinary(left, right, TermBinary.BinaryOpCode.EQ);
        }

        public static IList<Term> FunctionAssumptions(
            IEnumerable<Function> functions,
            IDictionary<Function, TermIdent> funInterpMapping,
            IDictionary<NamedDeclaration, Term> declToVCMapping,
            BoogieContextIsa boogieContext
        )
        {
            IList<Term> assumptions = new List<Term>();

            var converter = new PureToBoogieValConverter();

            foreach (Function f in functions)
            {
                #region context well-formed
                Term ctxWfLeft = new TermApp(IsaCommonTerms.Snd(boogieContext.funContext), new List<Term>() { new StringConst(f.Name) });
                Term ctxWfRight = IsaCommonTerms.SomeOption(funInterpMapping[f]);

                assumptions.Add(new TermBinary(ctxWfLeft, ctxWfRight, TermBinary.BinaryOpCode.EQ));
                #endregion                

                #region relation interpretation and pure function
                //TODO: unique naming scheme
                List<Identifier> boundParamVars = GetNames("farg", f.InParams.Count);
                
                TypeUtil.SplitTypeParams(f.TypeParameters, f.InParams.Select(v => v.TypedIdent.Type),
                    out List<TypeVariable> explicitTypeVars, out List<TypeVariable> implicitTypeVars);


                List<Identifier> boundTypeVars = GetNames("targ", f.TypeParameters.Count);
                
                
                IDictionary<TypeVariable, Term> substitution = new Dictionary<TypeVariable, Term>();
                int i = 0;
                foreach(var tv in f.TypeParameters)
                {
                    substitution.Add(tv, new TermIdent(boundTypeVars[i]));
                    i++;
                }
                
                var varSubstitution = new SimpleVarSubstitution<TypeVariable>(substitution);
                var typeIsaVisitor = new TypeIsaVisitor(varSubstitution);

                IEnumerable<Term> typeArgConstraints =
                        f.InParams.Where(v => !TypeUtil.IsPrimitive(v.TypedIdent.Type))
                            .Select((v, idx) => TermBinary.Eq(
                                IsaBoogieTerm.TypeToVal(boogieContext.absValTyMap, new TermIdent(boundParamVars[idx])),
                                IsaCommonTerms.SomeOption(typeIsaVisitor.Translate(v.TypedIdent.Type)))) ;

                List<Term> boogieFunTyArgs = boundTypeVars.Select(id => (Term) new TermIdent(id)).ToList();
                List<Term> boogieFunValArgs =
                    f.InParams.Select(
                        (v, idx) => converter.ConvertToBoogieVal(v.TypedIdent.Type, new TermIdent(boundParamVars[idx]))
                   ).ToList();

                Term left = new TermApp(funInterpMapping[f], new List<Term>()
                {
                    new TermList(boogieFunTyArgs),
                    new TermList(boogieFunValArgs)
                });

                Term right = IsaCommonTerms.SomeOption(
                    converter.ConvertToBoogieVal(f.OutParams.First().TypedIdent.Type,
                        new TermApp(declToVCMapping[f],
                            boundParamVars.Select(bv => (Term) new TermIdent(bv)).ToList()
                        )
                    )
                    );

                Term equation = TermBinary.Eq(left, right);

                if (typeArgConstraints.Any())
                {
                    var aggregatedAssms = typeArgConstraints.Aggregate((t1, t2) => TermBinary.And(t1,t2));
                    assumptions.Add(new TermQuantifier(TermQuantifier.QuantifierKind.ALL, boundParamVars.Union(boundTypeVars).ToList(), 
                        TermBinary.Implies(aggregatedAssms, equation)));
                }
                else
                { 
                    assumptions.Add(new TermQuantifier(TermQuantifier.QuantifierKind.ALL, boundParamVars.Union(boundTypeVars).ToList(), equation));
                }

                #endregion
            }

            return assumptions;
        }

        public static IDictionary<NamedDeclaration, Term> DeclToTerm(
            IEnumerable<NamedDeclaration> decls, 
            IEnumerable<Function> vcTypeDecls,
            VCTypeDeclTranslation typeDeclTranslation,
            IsaUniqueNamer namer)
        {
            var dict = new Dictionary<NamedDeclaration, Term>();

            foreach (NamedDeclaration decl in decls)
            {
                dict.Add(decl, IsaCommonTerms.TermIdentFromName(namer.GetName(decl, "vc_" + decl.Name)));
            }

            foreach(Function f in vcTypeDecls)
            {
                dict.Add(f, typeDeclTranslation.TranslateTypeDecl(f));
            }

            return dict;
        }

        public static IDictionary<Function, TermIdent> FunToTerm(IEnumerable<Function> funcs, IsaUniqueNamer namer)
        {
            var dict = new Dictionary<Function, TermIdent>();

            foreach (Function fun in funcs)
            {
                dict.Add(fun, IsaCommonTerms.TermIdentFromName(namer.GetName(fun, fun.Name)));
            }

            return dict;
        }

        public static IList<string> AssumptionLabels(string prefix, int fromIdx, int num)
        {
            Contract.Requires(prefix != null);
            Contract.Requires(num >= 0);
            Contract.Ensures(Contract.Result<IList<string>>().Count == num);

            return Enumerable.Range(fromIdx, num).Select((_, i) => prefix + i).ToList();
        }

        private static List<Identifier> GetNames(string baseName, int count)
        {
            var result = new List<Identifier>();
            for (int i = 0; i < count; i++)
            {
                result.Add(new SimpleIdentifier(baseName + i));
            }
            return result;
        }

    }
}
