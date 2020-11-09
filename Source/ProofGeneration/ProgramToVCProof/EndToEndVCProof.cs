﻿using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.BoogieIsaInterface.VariableTranslation;
using ProofGeneration.CFGRepresentation;
using ProofGeneration.Isa;
using ProofGeneration.IsaPrettyPrint;
using ProofGeneration.Util;
using ProofGeneration.VCProofGen;
using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Text;
using Microsoft.Boogie.VCExprAST;
using Type = Microsoft.Boogie.Type;

namespace ProofGeneration.ProgramToVCProof
{
    class EndToEndVCProof
    {
        private readonly BoogieMethodData methodData;

        private readonly IsaProgramRepr isaProgramRepr;

        private readonly IEnumerable<Function> vcFunctions;
        private readonly VCInstantiation<Block> vcinst;
        private readonly VCInstantiation<VCAxiom> vcinstAxiom;
        private readonly CFGRepr cfg;

        private readonly IVariableTranslationFactory varTranslationFactory;
        private readonly BasicCmdIsaVisitor basicCmdIsaVisitor;
        private readonly PureValueIsaTransformer pureValueIsaTransformer = new PureValueIsaTransformer();
        private readonly TypeIsaVisitor typeIsaVisitor;
        private readonly IsaUniqueNamer stateCorresNamer = new IsaUniqueNamer();

        private IDictionary<Axiom, int> axiomIdDict = null;

        private IEnumerable<Variable> ProgramVariables
        {
            get
            {
                return methodData.InParams.Union(methodData.Locals);
            }
        }

        private readonly IsaUniqueNamer membershipNamer = new IsaUniqueNamer();
        private readonly IList<LemmaDecl> membershipLemmas = new List<LemmaDecl>();

        private readonly BoogieContextIsa boogieContext;

        private readonly VCExpressionGenerator vcExprGen;
        private readonly TypePremiseEraserFactory eraserFactory;

        private readonly TermIdent normalInitState = IsaCommonTerms.TermIdentFromName("n_s");
        private readonly TermIdent finalState = IsaCommonTerms.TermIdentFromName("s'");
        private readonly TermIdent finalNode = IsaCommonTerms.TermIdentFromName("m'");

        private readonly string vcAssmName = "VC";
        private readonly string closedAssmName = "Closed";
        private readonly string finterpAssmName = "FInterp";
        private readonly string axiomAssmName = "Axioms";
        private readonly string paramsAssmName = "Params";
        private readonly string localVarsAssmName = "LocalVars";
        private readonly string RedAssmName = "Red";

        public EndToEndVCProof(
            BoogieMethodData methodData,
            IsaProgramRepr isaProgramRepr,
            IEnumerable<Function> vcFunctions, 
            VCInstantiation<Block> vcinst,
            VCInstantiation<VCAxiom> vcinstAxiom,
            CFGRepr cfg,
            IVariableTranslationFactory varTranslationFactory,
            TypePremiseEraserFactory eraserFactory,
            VCExpressionGenerator vcExprGen)
        {
            this.methodData = methodData;
            this.vcFunctions = vcFunctions;
            this.isaProgramRepr = isaProgramRepr;
            this.vcinst = vcinst;
            this.vcinstAxiom = vcinstAxiom;
            this.cfg = cfg;
            this.varTranslationFactory = varTranslationFactory;
            this.eraserFactory = eraserFactory;
            this.vcExprGen = vcExprGen;
            basicCmdIsaVisitor = new BasicCmdIsaVisitor(varTranslationFactory);
            typeIsaVisitor = new TypeIsaVisitor(varTranslationFactory.CreateTranslation().TypeVarTranslation);

            boogieContext = new BoogieContextIsa(
              IsaCommonTerms.TermIdentFromName("A"),
              IsaCommonTerms.TermIdentFromName("\\<Lambda>"),
              IsaCommonTerms.TermIdentFromName("\\<Gamma>"),
              IsaCommonTerms.TermIdentFromName("\\<Omega>")
              );
        }

        public IEnumerable<OuterDecl> GenerateProof()
        {
            List<OuterDecl> result = new List<OuterDecl>();
            AddMembershipLemmas();

            result.AddRange(membershipLemmas);
            result.AddRange(VCFunDefinitions().Values);
            result.AddRange(FunCorresLemmas().Values);
            result.Add(FinalLemma());
            return result;
        }

        private void AddMembershipLemmas()
        {
            //functions
            AddMembershipLemmas(methodData.Functions,
                isaProgramRepr.funcsDeclDef,
                d => new StringConst(d.Name),
                d => IsaBoogieTerm.FunDecl((Function)d, varTranslationFactory, false),
                false
                );
            //variables
            var varTranslation = varTranslationFactory.CreateTranslation().VarTranslation;
            Func<NamedDeclaration, Term> idOfVar =
                d =>
                {
                    if (varTranslation.TryTranslateVariableId((Variable) d, out Term varId))
                    {
                        return varId;
                    }
                    else
                    {
                        throw new ProofGenUnexpectedStateException(typeof(EndToEndVCProof),
                            "Could not retrieve variable id");
                    }
                };
                
            AddMembershipLemmas(methodData.InParams,
                isaProgramRepr.paramsDeclDef,
                idOfVar,
                d => IsaBoogieTerm.VarDecl((Variable)d, typeIsaVisitor, false),
                true);
            AddMembershipLemmas(methodData.Locals,
                isaProgramRepr.localVarsDeclDef,
                idOfVar,
                d => IsaBoogieTerm.VarDecl((Variable)d, typeIsaVisitor, false),
                true);
            AddAxiomMembershipLemmas();
        }

        private void AddMembershipLemmas(
            IEnumerable<NamedDeclaration> decls,
            Term declsDef,
            Func<NamedDeclaration, Term> nameOf,
            Func<NamedDeclaration, Term> declOf,
            bool isVariable)
        {
            foreach (var d in decls)
            {
                Term lhs = new TermApp(
                    isVariable ? IsaCommonTerms.TermIdentFromName("nth") : IsaCommonTerms.TermIdentFromName("map_of"),
                    new List<Term> { declsDef, nameOf(d) });
                Term rhs = isVariable ? declOf(d) : IsaCommonTerms.SomeOption(declOf(d));

                Term statement = new TermBinary(lhs, rhs, TermBinary.BinaryOpCode.EQ);
                Proof proof = new Proof(new List<string> { "by " + ProofUtil.Simp(declsDef + "_def") });
                membershipLemmas.Add(new LemmaDecl(MembershipName(d), statement, proof));
            }
        }

        private void AddAxiomMembershipLemmas()
        {
            axiomIdDict = new Dictionary<Axiom, int>();

            Term funContext = IsaCommonTerms.TermIdentFromName("\\<Gamma>");
            Term axiomSet = IsaCommonTerms.SetOfList(isaProgramRepr.axiomsDeclDef);
            Term axiomSat = IsaBoogieTerm.AxiomSat(boogieContext.absValTyMap, funContext, isaProgramRepr.axiomsDeclDef, normalInitState);
            int id = 0;
            foreach (var axiom in methodData.Axioms)
            {
                Term axiomTerm = basicCmdIsaVisitor.Translate(axiom.Expr);
                Term elemAssm = IsaCommonTerms.Elem(axiomTerm, axiomSet);

                Proof proof = new Proof(new List<string> { "by (simp add: " + isaProgramRepr.axiomsDeclDef + "_def)" });
                axiomIdDict.Add(axiom, id);
                membershipLemmas.Add(new LemmaDecl(MembershipName(axiom, id), elemAssm, proof));
                id++;
            }
        }

        private IDictionary<Function, OuterDecl> VCFunDefinitions()
        {
            return BasicUtil.ApplyFunDict(methodData.Functions, VCFunDefinition);
        }

        //VC function that represents f
        private OuterDecl VCFunDefinition(Function f)
        {
            IsaUniqueNamer uniqueNamer = new IsaUniqueNamer();
            
            //LHS of function definition "vc_fun boogie_fun arg1 arg2 ... argN = ..." 
            Term funTerm = IsaCommonTerms.TermIdentFromName(uniqueNamer.GetName(f, f.Name));
            IList<Term> argsLhs = new List<Term> { boogieContext.absValTyMap, funTerm };

            var vcVars = new List<VCExprVar>();
            var varToTerm = new Dictionary<VCExprVar, Term>();
            List<Term> vcValueParams = new List<Term>();
            foreach (var v in f.InParams)
            {
                Term vTerm = IsaCommonTerms.TermIdentFromName(uniqueNamer.GetName(v, v.Name));
                vcValueParams.Add(vTerm);
                VCExprVar vVcVar = vcExprGen.Variable(v.Name, v.TypedIdent.Type);
                vcVars.Add(vVcVar);
                varToTerm.Add(vVcVar, vTerm); 
            }
            
            TypeUtil.SplitTypeParams(f.TypeParameters, 
                f.InParams.Select(v => v.TypedIdent.Type), 
                out List<TypeVariable> _, 
                out List<TypeVariable> implicitTypeVars);

            TypeExtractorTranslator extractorTranslator = new TypeExtractorTranslator(boogieContext, varToTerm);
            List<Term> boogieTyParams = new List<Term>();
            var typeVarToTerm = new Dictionary<TypeVariable, Term>();
            TypePremiseEraserProvider eraserProvider = eraserFactory.NewEraser();
            VCExprVar dummyVar = vcExprGen.Variable("dummy", eraserProvider.AxiomBuilder.T);
            foreach (var typeVar in f.TypeParameters)
            {
                Term typeVarClosedIsa;
                
                if (implicitTypeVars.Contains(typeVar))
                {
                    VCExpr extractor = eraserProvider.BestTypeVarExtractor(
                        typeVar, 
                        dummyVar,
                        f.InParams.Select(v => v.TypedIdent.Type).ToList(), 
                        vcVars);

                    typeVarClosedIsa = extractorTranslator.TranslateExtractor(extractor);
                }
                else
                {
                    typeVarClosedIsa = IsaCommonTerms.TermIdentFromName(uniqueNamer.GetName(typeVar, typeVar.Name));
                    argsLhs.Add(typeVarClosedIsa); 
                }
                boogieTyParams.Add(IsaBoogieVC.ClosedToTy(typeVarClosedIsa));
                typeVarToTerm.Add(typeVar, typeVarClosedIsa);
            }
            
            //add values after type variables
            argsLhs.AddRange(vcValueParams);
            
                
            /* arguments used to invoke the Boogie function:
             * type parameters => use extractors
             * function values => same as for VC function, except for primitive typed arguments for which one must construct
             * the corersponding Boogie value
             */
            List<Term> boogieValParams =
                vcValueParams.Select((p, idx) =>
                {
                    var v = f.InParams[idx];
                    if (TypeUtil.IsPrimitive(v.TypedIdent.Type))
                    {
                        return pureValueIsaTransformer.ConstructValue(p, v.TypedIdent.Type);
                    }

                    return p;
                }).ToList();

            Term boogieFunApp = new TermApp(funTerm, new List<Term> { new TermList(boogieTyParams), new TermList(boogieValParams)}); 
            
            //RHS of function definition, case splitting on whether boogie function reduces
            Term res = IsaCommonTerms.TermIdentFromName(uniqueNamer.GetName("res", "res"));

            TypeIsaVisitor typeVisitorSubst = new TypeIsaVisitor(new SimpleVarSubstitution<TypeVariable>(typeVarToTerm), true);
            Type outputType = f.OutParams[0].TypedIdent.Type;
            Term outputTypeIsa = typeVisitorSubst.Translate(outputType);

            Term outputValueIfNotReduced = IsaBoogieVC.ValOfClosedTy(boogieContext.absValTyMap, outputTypeIsa);
            
            Term functionBody = new TermCaseOf(
                boogieFunApp,
                new List<Tuple<Term, Term>>()
                {
                    Tuple.Create(IsaCommonTerms.SomeOption(res), 
                        TypeUtil.IsPrimitive(outputType) ? pureValueIsaTransformer.DestructValue(res, outputType) : res),
                    Tuple.Create(IsaCommonTerms.NoneOption(),
                    TypeUtil.IsPrimitive(outputType) ? pureValueIsaTransformer.DestructValue(outputValueIfNotReduced, outputType) : outputValueIfNotReduced)
                }
                );

            return new FunDecl(VCFunName(f), null, new List<Tuple<IList<Term>, Term>>(){Tuple.Create(argsLhs, functionBody)});
        }

        private string VCFunName(Function f)
        {
            return "vc_fun_" + f.Name;
        }

        private IDictionary<Function, LemmaDecl> FunCorresLemmas()
        {
            return BasicUtil.ApplyFunDict(methodData.Functions, FunCorres);
        }

        private LemmaDecl FunCorres(Function f)
        {
            IsaUniqueNamer uniqueNamer = new IsaUniqueNamer();

            Term funTerm = IsaCommonTerms.TermIdentFromName(uniqueNamer.GetName(f, f.Name));
            #region vc function call
            IList<Term> vcFunArgs = new List<Term> { boogieContext.absValTyMap, funTerm};
            
            TypeUtil.SplitTypeParams(f.TypeParameters, f.InParams.Select(v => v.TypedIdent.Type), 
                out List<TypeVariable> explicitTypeVars, out List<TypeVariable> implicitTypeVars);

            vcFunArgs.AddRange(explicitTypeVars.Select(tv =>
                IsaBoogieVC.TyToClosed(IsaCommonTerms.TermIdentFromName(uniqueNamer.GetName(tv, tv.Name)))));
            
            var vcVars = new List<VCExprVar>();
            var varToTerm = new Dictionary<VCExprVar, Term>();
            var vcValueParams = new List<Term>();
            foreach (var v in f.InParams)
            {
                Term vTerm = IsaCommonTerms.TermIdentFromName(uniqueNamer.GetName(v, v.Name));
                vcValueParams.Add(vTerm);
                VCExprVar vVcVar = vcExprGen.Variable(v.Name, v.TypedIdent.Type);
                vcVars.Add(vVcVar);
                varToTerm.Add(vVcVar, vTerm); 
            }
            vcFunArgs.AddRange(vcValueParams);

            Term vc_f = IsaCommonTerms.TermIdentFromName(VCFunName(f));
            var vcFunctionCall = new TermApp(vc_f, vcFunArgs);
            #endregion
            
            #region Boogie function call
            var boogieTypeParams = f.TypeParameters.Select(tv => (Term) IsaCommonTerms.TermIdentFromName(uniqueNamer.GetName(tv, tv.Name))).ToList();
            var boogieTypeParamsList = new TermList(boogieTypeParams);
            var boogieValueParams = vcValueParams.Select((p, idx) =>
                {
                    var paramType = f.InParams[idx].TypedIdent.Type;
                    if (TypeUtil.IsPrimitive(paramType))
                        return pureValueIsaTransformer.ConstructValue(p, f.InParams[idx].TypedIdent.Type);
                        
                    return p;
                }).ToList();
            var boogieValueParamsList = new TermList(boogieValueParams);
            var boogieFunctionCall = new TermApp(funTerm, new List<Term>() {boogieTypeParamsList, boogieValueParamsList});
            #endregion
                
            #region lemma assumptions
            List<Term> assms = new List<Term>();
            List<string> assmLabels = new List<string>();
            string ClosedAssmLabel(int i) => "closed" + i;
            string TypeOfArgAssmLabel(int i) => "typeOfArg" + i;

            //funtion interpretation well-formed assumption
            assms.Add(IsaBoogieTerm.FunInterpSingleWf(boogieContext.absValTyMap, IsaBoogieTerm.FunDecl(f, varTranslationFactory, false), funTerm));
            assmLabels.Add(finterpAssmName);
            
            //type variables closed assumption
            List<string> closedAssmLabels = new List<string>();
            int closedIdx = 0;
            foreach(var t in boogieTypeParams)
            { 
                assms.Add(IsaBoogieTerm.IsClosedType(t));
                assmLabels.Add(ClosedAssmLabel(closedIdx)); 
                closedAssmLabels.Add(ClosedAssmLabel(closedIdx));
                closedIdx++;
            }
            
            //type of value arguments assumption
            var typeVariableSubst = new Dictionary<TypeVariable, Term>();
            {
                int idx = 0;
                foreach (var tv in f.TypeParameters)
                {
                    typeVariableSubst.Add(tv, boogieTypeParams[idx]);
                    idx++;
                }
            }

            var typeIsaFuncVisitor = new TypeIsaVisitor(new SimpleVarSubstitution<TypeVariable>(typeVariableSubst));
            var typeOfValAssms = new List<string>();
            {
                int idx = 0;
                foreach (var t in vcValueParams)
                {
                    var paramType = f.InParams[idx].TypedIdent.Type;
                    if (!TypeUtil.IsPrimitive(paramType))
                    {
                        assms.Add(
                            TermBinary.Eq(IsaBoogieTerm.TypeToVal(boogieContext.absValTyMap, t),
                                typeIsaFuncVisitor.Translate(paramType))
                        );
                        assmLabels.Add(TypeOfArgAssmLabel(idx));
                        typeOfValAssms.Add(TypeOfArgAssmLabel(idx));
                    }

                    idx++;
                }
            }
            #endregion

            #region lemma statement
            Type outputType = f.OutParams[0].TypedIdent.Type;

            Term ConstructOutputValue(Term rawOutputValue)
            {
                var result = rawOutputValue;
                if (TypeUtil.IsPrimitive(outputType))
                {
                    result = pureValueIsaTransformer.ConstructValue(result, outputType);
                }

                return result;
            }

            Term conclusion = TermBinary.Eq(boogieFunctionCall, IsaCommonTerms.SomeOption(ConstructOutputValue(vcFunctionCall)));
            #endregion

            #region lemma proof
            string zReturnVal = uniqueNamer.GetName("z", "z");
            var proofMethods = new List<string>()
            {
                "proof -",
                "from " + IsaPrettyPrinterHelper.SpaceAggregate(typeOfValAssms) + " " + finterpAssmName +
                " obtain " + zReturnVal + " where W:" + IsaPrettyPrinterHelper.Inner(
                    TermBinary.Eq(boogieFunctionCall,
                    IsaCommonTerms.SomeOption(ConstructOutputValue(IsaCommonTerms.TermIdentFromName(zReturnVal)))).ToString()),
                "  apply (simp only: fun_interp_single_wf.simps) ",
                "  apply (erule allE[where ?x=" + IsaPrettyPrinterHelper.Inner(boogieTypeParamsList.ToString()) + "])",
                "  apply (simp add: " + closedAssmLabels.SpaceAggregate() + ")",
                "  apply (erule allE[where ?x=" + IsaPrettyPrinterHelper.Inner(boogieValueParamsList.ToString()) + "])",
                (outputType.IsBool ? "using tbool_boolv" : "") + (outputType.IsInt ? "using tint_intv" : "") + " by auto"
            };
            
            //prove that one can express each implicit type variable using a corresponding extractor
            TypeExtractorTranslator extractorTranslator = new TypeExtractorTranslator(boogieContext, varToTerm);
            TypePremiseEraserProvider eraserProvider = eraserFactory.NewEraser();
            VCExprVar dummyVar = vcExprGen.Variable("dummy", eraserProvider.AxiomBuilder.T);
            List<Type> valueParamTypes = f.InParams.Select(v => v.TypedIdent.Type).ToList();

            var explicitTypeVarAssms = "";
            var proofMethodsExtractors = new List<string>();
            {
                int idx = 0;
                foreach (var tv in f.TypeParameters)
                {
                    if (implicitTypeVars.Contains(tv))
                    {
                        VCExpr extractor = eraserProvider.BestTypeVarExtractor(
                            tv,
                            dummyVar,
                            valueParamTypes,
                            vcVars
                        );
                        Term extractorTerm = extractorTranslator.TranslateExtractor(extractor);
                        
                        string prefix = "moreover from ";
                        if (idx == 0)
                        {
                            prefix = "from ";
                        }
                        proofMethodsExtractors.Add(
                            prefix + IsaPrettyPrinterHelper.SpaceAggregate(typeOfValAssms) + " have " +
                            " \" " + TermBinary.Eq(boogieTypeParams[idx], IsaBoogieVC.ClosedToTy(extractorTerm)) + "\"" +
                            " using  closed_inv2 " + ClosedAssmLabel(idx) + " by auto"
                        );
                    }
                    else
                    {
                        explicitTypeVarAssms = explicitTypeVarAssms + " " + "closed_inv2_2[OF " + ClosedAssmLabel(idx)+"]";
                    }

                    idx++;
                }
            }
            
            proofMethods.AddRange(proofMethodsExtractors);
            
            proofMethods.Add((proofMethodsExtractors.Count > 1 ? "ultimately " : "from this ") + 
                             " show ?thesis using " + IsaPrettyPrinterHelper.SpaceAggregate(typeOfValAssms) + explicitTypeVarAssms);
            proofMethods.Add("by (simp add: W) qed");


            return new LemmaDecl(FunCorresName(f), ContextElem.CreateWithAssumptions(assms,assmLabels), conclusion, 
                new Proof(proofMethods));
            #endregion
        }

        private LemmaDecl FinalLemma()
        {
            var uniqueNamer = new IsaUniqueNamer();
            //adjust declToVCMapping to include vc type declarations
            var typeDeclTranslation = new GenericTypeDeclTranslation(uniqueNamer); 
            var declToVCMapping = 
                LemmaHelper.DeclToTerm(ProgramVariables, vcFunctions, typeDeclTranslation, uniqueNamer);
            List<Identifier> declIds = declToVCMapping.Values.Select(t => ((TermIdent) t).id).ToList();
            var absValType = new VarType("a");
            PureTyIsaTransformer concretePureTyIsaTransformer = LemmaHelper.ConretePureTyIsaTransformer(absValType);
            List<TypeIsa> declTypes = declToVCMapping.Keys.Select(nd => concretePureTyIsaTransformer.Translate(nd)).ToList(); 
            //handle Boogie functions separately, since VC version has different type
            //TODO: find cleaner way to handle this (PassiveLemmaManager also uses such a suboptimal solution)
            foreach (var boogieFun in methodData.Functions)
            {
                var id = new SimpleIdentifier(uniqueNamer.GetName(boogieFun, "vc_" + boogieFun.Name));
                declIds.Add(id);
                declToVCMapping.Add(boogieFun, new TermIdent(id));
                TypeUtil.SplitTypeParams(boogieFun.TypeParameters, boogieFun.InParams.Select(v => v.TypedIdent.Type),
                    out List<TypeVariable> explicitTypeVars, out _);

                TypeIsa typeIsa = concretePureTyIsaTransformer.Translate(new Function(null, boogieFun.Name,
                    explicitTypeVars, boogieFun.InParams, boogieFun.OutParams[0]));
                declTypes.Add(typeIsa);
            }
            
            Term vcAssmWithoutAxioms = vcinst.GetVCObjInstantiation(cfg.entry, declToVCMapping);

            Term vcAssm = vcinstAxiom.Keys.Reverse().Aggregate(vcAssmWithoutAxioms, (current, vcAx) => 
                new TermBinary(vcinstAxiom.GetVCObjInstantiation(vcAx, declToVCMapping), current, TermBinary.BinaryOpCode.META_IMP));

            /*List<TypeIsa> declTypes = methodData.Functions.Select(f => pureTyIsaTransformer.Translate(f)).ToList();
            declTypes.AddRange(ProgramVariables.Select(v => pureTyIsaTransformer.Translate(v)));*/
            vcAssm = TermQuantifier.MetaAll(declIds, declTypes, vcAssm);

            Term funContext = new TermTuple(new List<Term> { isaProgramRepr.funcsDeclDef, boogieContext.funContext });

            Term closedAssm = LemmaHelper.ClosednessAssumption(boogieContext.absValTyMap);
            Term finterpAssm = IsaBoogieTerm.FunInterpWf(boogieContext.absValTyMap, isaProgramRepr.funcsDeclDef, boogieContext.funContext);
            //need to explicitly give type for normal state, otherwise Isabelle won't know that the abstract value type is the same as used in the VC
            Term axiomAssm = IsaBoogieTerm.AxiomSat(boogieContext.absValTyMap, funContext, isaProgramRepr.axiomsDeclDef, 
                new TermWithExplicitType(normalInitState, IsaBoogieType.NormalStateType(absValType)));
            Term paramsAssm = IsaBoogieTerm.StateWf(boogieContext.absValTyMap, boogieContext.rtypeEnv, isaProgramRepr.paramsDeclDef, normalInitState);
            Term localVarsAssm = IsaBoogieTerm.StateWf(boogieContext.absValTyMap, boogieContext.rtypeEnv, isaProgramRepr.localVarsDeclDef, normalInitState);
            Term multiRed = IsaBoogieTerm.RedCFGMulti(
                new BoogieContextIsa(
                    boogieContext.absValTyMap,                  
                    IsaCommonTerms.AppendList(isaProgramRepr.paramsDeclDef, isaProgramRepr.localVarsDeclDef),
                    new TermTuple(new List<Term> { isaProgramRepr.funcsDeclDef, boogieContext.funContext }),
                    boogieContext.rtypeEnv),
                isaProgramRepr.cfgDeclDef,
                IsaBoogieTerm.CFGConfigNode(new NatConst(cfg.GetUniqueIntLabel(cfg.entry)), IsaBoogieTerm.Normal(normalInitState)),
                IsaBoogieTerm.CFGConfig(finalNode, finalState)
                );

            Term conclusion = new TermBinary(finalState, IsaBoogieTerm.Failure(), TermBinary.BinaryOpCode.NEQ);

            var contextElem = ContextElem.CreateWithAssumptions(
                new List<Term> { vcAssm, closedAssm, finterpAssm, axiomAssm, paramsAssm, localVarsAssm, multiRed },
                new List<string> { vcAssmName, closedAssmName, finterpAssmName, axiomAssmName, paramsAssmName, localVarsAssmName, RedAssmName });
            return new LemmaDecl("endToEnd", contextElem, conclusion, FinalProof());
        }

        private Proof FinalProof()
        {
            var sb = new StringBuilder();
            sb.AppendLine("proof -");

            //functions
            foreach(Function f in methodData.Functions)
            {
                Term fStringConst = new StringConst(f.Name);
                sb.Append("let " + FunAbbrev(f) + " = ");
                sb.AppendInner("opaque_comp the " + boogieContext.funContext + " " + fStringConst);
                sb.AppendLine();
                sb.Append("from " + finterpAssmName + " have " + InterpMemName(f) + ":");
                sb.AppendInner(
                new TermBinary(new TermApp(boogieContext.funContext, fStringConst), 
                    IsaCommonTerms.SomeOption(IsaCommonTerms.TermIdentFromName(FunAbbrev(f))),
                    TermBinary.BinaryOpCode.EQ).ToString());
                sb.AppendLine();
                sb.AppendLine("apply " + ProofUtil.SimpOnly("opaque_comp_def"));
                sb.AppendLine("using " + "fun_interp_wf_def " + MembershipName(f) + " option.sel by metis");

                /*
                sb.Append("from " + finterpAssmName + " have " + WfName(f) + ":");
                sb.AppendInner(IsaBoogieTerm.FunInterpSingleWf(f, boogieContext.absValTyMap, IsaCommonTerms.TermIdentFromName(FunAbbrev(f)), varTranslationFactory).ToString());
                sb.AppendLine();
                sb.AppendLine("apply " + ProofUtil.SimpOnly("opaque_comp_def"));
                sb.AppendLine("using " + "fun_interp_wf_def " + MembershipName(f) + " option.sel by metis");
                sb.AppendLine();
                */
            }

            //variables
            AppendStateCorres(sb, paramsAssmName, methodData.InParams);
            AppendStateCorres(sb, localVarsAssmName, methodData.Locals);

            //axioms
            Term funContext = new TermTuple(new List<Term> { isaProgramRepr.funcsDeclDef, boogieContext.funContext });

            foreach(Axiom ax in methodData.Axioms)
            {
                Term axiomTerm = basicCmdIsaVisitor.Translate(ax.Expr);
                Term exprEvaluatesToTrue = IsaBoogieTerm.RedExpr(boogieContext, axiomTerm, normalInitState, IsaBoogieTerm.BoolVal(true));
                sb.Append("have "+ EvaluationName(ax) + ":" + " ");
                sb.AppendInner(exprEvaluatesToTrue.ToString()); sb.AppendLine();
                sb.AppendLine("by (rule axioms_sat_mem[OF " + MembershipName(ax) + " " + axiomAssmName +"])");
            }
            sb.AppendLine();

            //store function theorems
            /*
            sb.AppendLine("ML_prf \\<open>");
            sb.AppendLine();
            foreach(Function f in methodData.Functions)
            {
                sb.AppendLine("val " + FunCorresName(f, true) + " = " + "@{thm " + ProofUtil.OF(FunCorresName(f), WfName(f)) + "}");
                sb.AppendLine("val " + InterpMemName(f, true) + " = " + "@{thm " + InterpMemName(f) + "}");
            }
            string storedFunctionThms = "storedFunctionThms";
            string interpLemmasList = "[" + IsaPrettyPrinterHelper.CommaAggregate(methodData.Functions.Select(f => FunCorresName(f, true))) + ", " +
    IsaPrettyPrinterHelper.CommaAggregate(methodData.Functions.Select(f => InterpMemName(f, true))) + "]";

            sb.AppendLine("val " + storedFunctionThms + " = " + interpLemmasList);
            sb.AppendLine("\\<close>");
            */
            
            //conclusion
            sb.Append("show ");
            sb.AppendInner(new TermBinary(finalState, IsaBoogieTerm.Failure(), TermBinary.BinaryOpCode.NEQ).ToString());
            sb.AppendLine();
     
            sb.AppendLine("apply (rule passification.method_verifies[OF _ " + RedAssmName + "])");
            sb.AppendLine("apply " + ProofUtil.SimpOnly("passification_def"));
            sb.AppendLine("apply (intro conjI)");

            foreach (Function f in methodData.Functions)
            {
                //TODO: Use stored ML theorems to avoid re-instantiation
                sb.AppendLine("apply " + ProofUtil.Simp(InterpMemName(f)));
                sb.AppendLine("apply (rule+)");
                sb.AppendLine(
                    ProofUtil.MLTactic("vc_fun_corres_tac " + MLUtil.ContextAntiquotation() + " " + MLUtil.IsaToMLThm(FunCorresName(f)) + " " +
                              MLUtil.IsaToMLThm(finterpAssmName) + " " + MLUtil.IsaToMLThm(MembershipName(f)) + " " +
                              MLUtil.IsaToMLThm(InterpMemName(f)), 1));
                //sb.AppendLine(ProofUtil.OF(FunCorresName(f), WfName(f)));
            }

            foreach (Variable v in ProgramVariables)
            {
                string evalTac = "rule " + ProofUtil.OF("HOL.conjunct1", StateCorresName(v));
                string typeTac = TypeUtil.IsPrimitive(v.TypedIdent.Type)
                    ? ""
                    : " , rule " + ProofUtil.OF("HOL.conjunct2", StateCorresName(v));
                sb.AppendLine("apply (" + evalTac + typeTac + ")");
            }

            sb.AppendLine("apply " + ProofUtil.Simp(closedAssmName));
            sb.AppendLine("apply (rule " + vcAssmName + ")");

            /* TODO
            foreach(Axiom ax in methodData.Axioms)
            {
                sb.AppendLine("apply " + ProofUtil.SimpOnly(vcinstAxiom.GetVCObjNameRef(ax) + "_def"));
                sb.AppendLine("apply (rule expr_to_vc[OF " + EvaluationName(ax) + "])");               
                sb.AppendLine("apply(tactic \\<open> b_vc_expr_rel_tac @{context} " + storedFunctionThms + " [] 1 \\<close>)");
            }
            */
            sb.AppendLine("done");
            sb.AppendLine("qed");

            return new Proof(new List<string> { sb.ToString() });
        }

        private void AppendStateCorres(StringBuilder sb, string assm, IEnumerable<Variable> vars)
        {
            var variableTranslation = varTranslationFactory.CreateTranslation().VarTranslation;
            foreach(var v in vars)
            {
                if (variableTranslation.TryTranslateVariableId(v, out Term vNatConst))
                {
                    sb.Append("from " + assm + " have " + StateCorresName(v) + ":");
                    Term stateEval = new TermApp(normalInitState, vNatConst);
                    Term stateEvalRhs = IsaCommonTerms.SomeOption(
                        pureValueIsaTransformer.ConstructValue(
                            pureValueIsaTransformer.DestructValue(
                                IsaCommonTerms.TheOption(stateEval),
                                v.TypedIdent.Type), 
                            v.TypedIdent.Type)
                            );
                    Term stateEvalType =
                        TermBinary.Eq(
                            IsaBoogieTerm.TypeToVal(boogieContext.absValTyMap, IsaCommonTerms.TheOption(stateEval)),
                            typeIsaVisitor.Translate(v.TypedIdent.Type));
                    sb.AppendInner(TermBinary.And(TermBinary.Eq(stateEval, stateEvalRhs), 
                        stateEvalType).ToString());
                    sb.AppendLine();
                    sb.AppendLine("apply " + ProofUtil.SimpOnly("state_typ_wf_def"));
                    sb.AppendLine("apply (erule allE, erule allE, erule impE, rule " + MembershipName(v) +")");
                    sb.AppendLine("by (fastforce dest: tint_intv tbool_boolv)");
                }
            }
        }

        private string MembershipName(NamedDeclaration d)
        {
            var name = membershipNamer.GetName(d, d.Name);
            if(d is Function)
            {
                return "mfun_" + name;
            } else
            {
                return "m_" + name;
            }
        }

        private string MembershipName(Axiom a)
        {
            Contract.Requires(axiomIdDict != null);
            return "ma_" + axiomIdDict[a];
        }

        private string EvaluationName(Axiom a)
        {
            Contract.Requires(axiomIdDict != null);
            return "ea_" + axiomIdDict[a];
        }

        private string MembershipName(Axiom a, int id)
        {
            return "ma_" + id;
        }

        private string FunAbbrev(Function f)
        {
            return "?" + f.Name;
        }

        private string InterpMemName(Function f, bool ML = false)
        {
            return "im_" + f.Name + (ML ? "_ml" : "");
        }

        private string WfName(Function f)
        {
            return "i_" + f.Name;
        }

        private string FunCorresName(Function f, bool ML = false)
        {
            return "vc_" + f.Name + "_corres" + (ML ? "_ml" : "");
        }

        private string StateCorresName(Variable v)
        {
            return "sc_" + stateCorresNamer.GetName(v, v.Name);
        }

    }
}
