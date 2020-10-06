using Microsoft.Boogie;
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
        private readonly PureTyIsaTransformer pureTyIsaTransformer = new PureTyIsaTransformer();
        private readonly TypeIsaVisitor typeIsaVisitor;

        private IDictionary<Axiom, int> axiomIdDict = null;

        private IEnumerable<Variable> ProgramVariables
        {
            get
            {
                return methodData.InParams.Union(methodData.Locals);
            }
        }

        private readonly IList<LemmaDecl> membershipLemmas = new List<LemmaDecl>();

        private readonly BoogieContextIsa boogieContext;

        private readonly TermIdent normalInitState = IsaCommonTerms.TermIdentFromName("n_s");
        private readonly TermIdent finalState = IsaCommonTerms.TermIdentFromName("s'");
        private readonly TermIdent finalNode = IsaCommonTerms.TermIdentFromName("m'");

        private readonly string vcAssmName = "VC";
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
            IVariableTranslationFactory varTranslationFactory)
        {
            this.methodData = methodData;
            this.vcFunctions = vcFunctions;
            this.isaProgramRepr = isaProgramRepr;
            this.vcinst = vcinst;
            this.vcinstAxiom = vcinstAxiom;
            this.cfg = cfg;
            this.varTranslationFactory = varTranslationFactory;
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

        private IDictionary<Function, DefDecl> VCFunDefinitions()
        {
            return BasicUtil.ApplyFunDict(methodData.Functions, VCFunDefinition);
        }

        //VC function that represents f
        private DefDecl VCFunDefinition(Function f)
        {
            IsaUniqueNamer uniqueNamer = new IsaUniqueNamer();

            Term funTerm = IsaCommonTerms.TermIdentFromName(uniqueNamer.GetName(f, f.Name));
            IList<Term> args = new List<Term> { funTerm };

            IList<Term> paramsTerm = f.InParams.Select(v => (Term) IsaCommonTerms.TermIdentFromName(uniqueNamer.GetName(v, v.Name))).ToList();
            args.AddRange(paramsTerm);

            IEnumerable<Term> paramsVal = paramsTerm.Select((p, idx) => pureValueIsaTransformer.ConstructValue(p, f.InParams[idx].TypedIdent.Type));

            Term outputVal = IsaCommonTerms.TheOption(new TermApp(funTerm, new TermList(paramsVal.ToList())));
            Term pureOutputVal = pureValueIsaTransformer.DestructValue(outputVal, f.OutParams[0].TypedIdent.Type);

            string name = VCFunName(f);

            return new DefDecl(name, Tuple.Create(args, pureOutputVal));
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
            IList<Term> args = new List<Term> { funTerm };

            IList<Identifier> paramsId = f.InParams.Select(v => (Identifier) new SimpleIdentifier(uniqueNamer.GetName(v, v.Name))).ToList();
            var paramsTerm = paramsId.Select(id => (Term) new TermIdent(id));
            args.AddRange(paramsTerm);

            IEnumerable<Term> paramsVal = paramsTerm.Select((p, idx) => pureValueIsaTransformer.ConstructValue(p, f.InParams[idx].TypedIdent.Type));

            Term vc_f = IsaCommonTerms.TermIdentFromName(VCFunName(f));

            Term assm = IsaBoogieTerm.FunInterpSingleWf(boogieContext.absValTyMap, IsaBoogieTerm.FunDecl(f, varTranslationFactory, false), funTerm);

            Term lhs = new TermApp(funTerm, new TermList(paramsVal.ToList()));
            Term rhs = IsaCommonTerms.SomeOption(pureValueIsaTransformer.ConstructValue(new TermApp(vc_f, args), f.OutParams[0].TypedIdent.Type));
            Term innerStatement = new TermBinary(lhs, rhs, TermBinary.BinaryOpCode.EQ);

            var paramTypesIsa = f.InParams.Select(p => pureTyIsaTransformer.Translate(p.TypedIdent.Type)).ToList();
            Term conclusion = TermQuantifier.ForAll(paramsId, paramTypesIsa, innerStatement);

            //proof
            var proofMethods = new List<string>()
            {
                "proof((rule allI)+)",
                "fix " + IsaPrettyPrinterHelper.SpaceAggregate(paramsTerm.Select(p => p.ToString()).ToList()),
                "show " + IsaPrettyPrinterHelper.Inner(innerStatement.ToString()),
                "using assms",
                "apply simp",
                "apply (erule allE[where ?x=" + IsaPrettyPrinterHelper.Inner((new TermList(paramsVal.ToList())).ToString()) + "])",
                "using tint_intv tbool_boolv " + vc_f.ToString()+"_def "+ "by fastforce",
                "qed"
            };

            return new LemmaDecl(FunCorresName(f), ContextElem.CreateWithAssumptions(assm), conclusion, new Proof(proofMethods));
        }

        private LemmaDecl FinalLemma()
        {
            var uniqueNamer = new IsaUniqueNamer();
            //adjust declToVCMapping to include vc type declarations
            var typeDeclTranslation = new GenericTypeDeclTranslation(uniqueNamer); 
            var declToVCMapping = 
                LemmaHelper.DeclToTerm(((IEnumerable<NamedDeclaration>) methodData.Functions).Union(ProgramVariables), vcFunctions, typeDeclTranslation, uniqueNamer);
            Term vcAssmWithoutAxioms = vcinst.GetVCObjInstantiation(cfg.entry, declToVCMapping);

            Term vcAssm = vcinstAxiom.Keys.Reverse().Aggregate(vcAssmWithoutAxioms, (current, vcAx) => 
                new TermBinary(vcinstAxiom.GetVCObjInstantiation(vcAx, declToVCMapping), current, TermBinary.BinaryOpCode.META_IMP));

            List<Identifier> declIds = declToVCMapping.Values.Select(t => ((TermIdent) t).id).ToList();
            var absValType = new VarType("a");
            PureTyIsaTransformer concretePureTyIsaTransformer = LemmaHelper.ConretePureTyIsaTransformer(absValType);
            List<TypeIsa> declTypes = declToVCMapping.Keys.Select(nd => concretePureTyIsaTransformer.Translate(nd)).ToList(); 
            /*List<TypeIsa> declTypes = methodData.Functions.Select(f => pureTyIsaTransformer.Translate(f)).ToList();
            declTypes.AddRange(ProgramVariables.Select(v => pureTyIsaTransformer.Translate(v)));*/
            vcAssm = TermQuantifier.MetaAll(declIds, declTypes, vcAssm);

            Term funContext = new TermTuple(new List<Term> { isaProgramRepr.funcsDeclDef, boogieContext.funContext });

            Term finterpAssm = IsaBoogieTerm.FunInterpWf(boogieContext.absValTyMap, isaProgramRepr.funcsDeclDef, boogieContext.funContext);
            Term axiomAssm = IsaBoogieTerm.AxiomSat(boogieContext.absValTyMap, funContext, isaProgramRepr.axiomsDeclDef, normalInitState);
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
                new List<Term> { vcAssm, finterpAssm, axiomAssm, paramsAssm, localVarsAssm, multiRed },
                new List<string> { vcAssmName, finterpAssmName, axiomAssmName, paramsAssmName, localVarsAssmName, RedAssmName });
            return new LemmaDecl("endToEnd", contextElem, conclusion, new Proof(new List<string>()));
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

                sb.Append("from " + finterpAssmName + " have " + WfName(f) + ":");
                sb.AppendInner(IsaBoogieTerm.FunInterpSingleWf(f, boogieContext.absValTyMap, IsaCommonTerms.TermIdentFromName(FunAbbrev(f)), varTranslationFactory).ToString());
                sb.AppendLine();
                sb.AppendLine("apply " + ProofUtil.SimpOnly("opaque_comp_def"));
                sb.AppendLine("using " + "fun_interp_wf_def " + MembershipName(f) + " option.sel by metis");
                sb.AppendLine();
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

            //conclusion
            sb.Append("show ");
            sb.AppendInner(new TermBinary(finalState, IsaBoogieTerm.Failure(), TermBinary.BinaryOpCode.NEQ).ToString());
            sb.AppendLine();
     
            sb.AppendLine("apply (rule passification.method_verifies[OF _ " + RedAssmName + "])");
            sb.AppendLine("apply " + ProofUtil.SimpOnly("passification_def"));

            foreach(Function f in methodData.Functions)
            {
                //TODO: Can be more precise with conjI tactic instead of using +, ?;
                //TODO: Use stored ML theorems to avoid re-instantiation
                sb.AppendLine("apply (" + ProofUtil.TryRepeatConjI() + ", " + ProofUtil.Simp(InterpMemName(f)) + ", " + ProofUtil.TryRepeatConjI() +", " + 
                    "rule " + FunCorresName(f)+"[OF "+ WfName(f) +"])");
            }

            int numProgramVars = ProgramVariables.Count();
            int idx = 0;
            foreach(Variable v in ProgramVariables)
            {
                string conjIOpt = "";
                if(idx != numProgramVars-1)
                {
                    conjIOpt = "(rule conjI)+, ";
                }
                idx++;

                sb.AppendLine("apply (" + conjIOpt + " rule " + StateCorresName(v)+ ")");
            }

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
            foreach(var v in vars)
            {
                Term vStringConst = new StringConst(v.Name);
                sb.Append("from " + assm + " have " + StateCorresName(v) + ":");
                Term lhs = new TermApp(normalInitState, vStringConst);
                Term rhs = IsaCommonTerms.SomeOption(
                    pureValueIsaTransformer.ConstructValue(
                        pureValueIsaTransformer.DestructValue(
                            IsaCommonTerms.TheOption(lhs),
                            v.TypedIdent.Type), 
                        v.TypedIdent.Type)
                        );
                sb.AppendInner(new TermBinary(lhs, rhs, TermBinary.BinaryOpCode.EQ).ToString());
                sb.AppendLine();
                sb.AppendLine("apply " + ProofUtil.SimpOnly("state_typ_wf_def"));
                sb.AppendLine("apply (erule allE, erule allE, erule impE, rule " + MembershipName(v) +")");
                sb.AppendLine("by (fastforce dest: tint_intv tbool_boolv)");
            }
        }

        private string MembershipName(NamedDeclaration d)
        {
            if(d is Function)
            {
                return "mfun_" + d.Name;
            } else
            {
                return "m_" + d.Name;
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
            return "sc_" + v.Name;
        }

    }
}
