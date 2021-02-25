using System;
using System.Collections;
using Microsoft.Boogie;
using ProofGeneration.Isa;
using ProofGeneration.Util;
using ProofGeneration.VCProofGen;
using System.Collections.Generic;
using System.ComponentModel.Design.Serialization;
using System.Linq;
using System.Diagnostics.Contracts;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.BoogieIsaInterface.VariableTranslation;

namespace ProofGeneration.ProgramToVCProof
{
    static class LemmaHelper
    {
        private static readonly PureToBoogieValConverter pureToBoogieValConverter = new PureToBoogieValConverter();

        public static bool FinalStateIsMagic(Block block)
        {
            return
                block.Cmds.Any(cmd =>
                {
                    return cmd != null && cmd is PredicateCmd predCmd && predCmd.Expr is LiteralExpr predCond && predCond.IsFalse;
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

        public static Term LocalStateVariableAssumption(Variable v, 
            Term varContext,
            Term state,
            IDictionary<NamedDeclaration, Term> declToVCMapping,
            IVariableTranslation<Variable> varTranslation)
        {
            return LocalStateVariableAssumption(v, varContext, state, declToVCMapping[v], varTranslation);
        }
        
        public static Term VariableTypeAssumption(
            Variable v,
            Term vcVar,
            TypeIsaVisitor typeIsaVisitor,
            Term absValTyMap)
        {
            Term left = IsaBoogieTerm.TypeToVal(absValTyMap, vcVar);
            Term right = typeIsaVisitor.Translate(v.TypedIdent.Type);
            return TermBinary.Eq(left, right);
        }

        /// <summary>
        /// Returns type visitor that contains the type variables of f in the context
        /// </summary>
        public static TypeIsaVisitor FunTypeIsaVisitor(Function f, IVariableTranslationFactory varTranslationFactory)
        {
            IVariableTranslation<TypeVariable> typeVarTranslation = varTranslationFactory.CreateEmptyTranslation().TypeVarTranslation;
            /*
             * types variables are numbered as they appear in the list as opposed to type variables appearing later having a smaller number
             * that's the reason the loop iterates in reverse order
             */
            foreach(TypeVariable tv in ((IEnumerable<TypeVariable>) f.TypeParameters).Reverse())
            {
                typeVarTranslation.AddBoundVariable(tv);
            }
            
            return new TypeIsaVisitor(typeVarTranslation);
        }

        public static Term LocalStateVariableAssumption(Variable v, Term varContext,  Term normalState, Term vcVar, IVariableTranslation<Variable> varTranslation)
        {
            if (varTranslation.TryTranslateVariableId(v, out Term varId, out bool isBoundVar) && !isBoundVar)
            {
                Term left = IsaBoogieTerm.LookupVar(varContext, normalState, varId); 
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

        public static Term VarContextTypeAssumption(Variable v, Term varContext, TypeIsaVisitor typeIsaVisitor)
        {
            Term left = new TermApp(varContext, new StringConst(v.Name));
            Term right = IsaCommonTerms.SomeOption(typeIsaVisitor.Translate(v.TypedIdent.Type));
            return new TermBinary(left, right, TermBinary.BinaryOpCode.EQ);
        }

        public static Term FunctionCtxtWfAssm(Function f,
            IDictionary<Function, TermIdent> funInterpMapping,
            BoogieContextIsa boogieContext
            )
        {
            Term ctxWfLeft = new TermApp(boogieContext.funContext, new List<Term>() { new StringConst(f.Name) });
            Term ctxWfRight = IsaCommonTerms.SomeOption(funInterpMapping[f]);

            return new TermBinary(ctxWfLeft, ctxWfRight, TermBinary.BinaryOpCode.EQ);
        }
        public static Term FunctionVcCorresAssm(
            Function f,
            IDictionary<Function, TermIdent> funInterpMapping,
            IDictionary<NamedDeclaration, Term> declToVCMapping,
            BoogieContextIsa boogieContext
        )
        {
            var converter = new PureToBoogieValConverter();

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
                    f.InParams
                        .Select((v, idx) => 
                            !TypeUtil.IsPrimitive(v.TypedIdent.Type) ? TermBinary.Eq(
                            IsaBoogieTerm.TypeToVal(boogieContext.absValTyMap, new TermIdent(boundParamVars[idx])),
                            typeIsaVisitor.Translate(v.TypedIdent.Type)) : null)
                        .Where(t => t != null );

            List<Term> boogieFunTyArgs = boundTypeVars.Select(id => (Term) new TermIdent(id)).ToList();
            List<Term> vcFunTyArgs = new List<Term>();
            f.TypeParameters.ZipDo(boogieFunTyArgs, (tv, tvTerm) =>
            {
                if (explicitTypeVars.Contains(tv))
                    vcFunTyArgs.Add(IsaBoogieVC.TyToClosed(tvTerm));
            });
            
            List<Term> boogieFunValArgs =
                f.InParams.Select(
                    (v, idx) => converter.ConvertToBoogieVal(v.TypedIdent.Type, new TermIdent(boundParamVars[idx]))
               ).ToList();

            Term left = new TermApp(funInterpMapping[f], new List<Term>()
            {
                new TermList(boogieFunTyArgs),
                new TermList(boogieFunValArgs)
            });

            Term vcFunApp =
                new TermApp(declToVCMapping[f],
                    vcFunTyArgs.Union(
                        boundParamVars.Select(bv => (Term) new TermIdent(bv)).ToList()
                    ).ToList());

            var outputType = f.OutParams.First().TypedIdent.Type;

            Term right = IsaCommonTerms.SomeOption(
                converter.ConvertToBoogieVal(outputType,
                    vcFunApp)
            );
            
            Term equation = TermBinary.Eq(left, right);

            Term conclusion;
            if (!TypeUtil.IsPrimitive(outputType))
            {
                //if type is not primitive, then the type information is not yet included

                conclusion = TermBinary.And(equation, 
                    TermBinary.Eq(
                        IsaBoogieTerm.TypeToVal(boogieContext.absValTyMap, vcFunApp), 
                        typeIsaVisitor.Translate(outputType)
                        ));
            }
            else
            {
                conclusion = equation;
            }
            
            if (typeArgConstraints.Any())
            {
                var aggregatedAssms = typeArgConstraints.Aggregate((t1, t2) => TermBinary.And(t2,t1));

                if (boogieFunTyArgs.Any())
                {
                    var closednessAssms = boogieFunTyArgs.Select(t1 => IsaBoogieTerm.IsClosedType(t1))
                        .Aggregate((t1, t2) => TermBinary.And(t2, t1));
                    return new TermQuantifier(TermQuantifier.QuantifierKind.META_ALL, boundParamVars.Union(boundTypeVars).ToList(), 
                        TermBinary.MetaImplies(closednessAssms, TermBinary.MetaImplies(aggregatedAssms, conclusion)));
                }

                return new TermQuantifier(TermQuantifier.QuantifierKind.META_ALL, boundParamVars.Union(boundTypeVars).ToList(), 
                    TermBinary.MetaImplies(aggregatedAssms, conclusion));
            }

            if (boundParamVars.Any())
            {
                return new TermQuantifier(TermQuantifier.QuantifierKind.META_ALL, boundParamVars.Union(boundTypeVars).ToList(), conclusion);
            }

            return conclusion;
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
                if (typeDeclTranslation.TryTranslateTypeDecl(f, out Term result))
                {
                    dict.Add(f, result);
                }
                else
                {
                    throw new ProofGenUnexpectedStateException(typeof(LemmaHelper), "Could not find vc function instantiation");
                }

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

        //returns PureTyIsaTransformer that instantiates U and T with the concrete instantiations
        public static PureTyIsaTransformer ConretePureTyIsaTransformer(TypeIsa abstractValueType)
        {
            //instantiate type in VC representing Boogie values with Boogie value type
            //instantiate type in VC representing Boogie types with Boogie closed type
            return new PureTyIsaTransformer(IsaBoogieType.ValType(abstractValueType), IsaBoogieVC.BoogieClosedType());
        }

    }
}
