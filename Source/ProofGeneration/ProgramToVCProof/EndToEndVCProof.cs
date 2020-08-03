using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;
using ProofGeneration.BoogieIsaInterface;
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
        private readonly IEnumerable<Function> functions;
        private readonly IEnumerable<Axiom> axioms;
        private readonly IEnumerable<Variable> parameters;
        private readonly IEnumerable<Variable> localVars;
        private readonly IsaProgramRepr isaProgramRepr;
        private readonly VCInstantiation<Block> vcinst;
        private readonly VCInstantiation<Axiom> vcinstAxiom;
        private readonly VCExpr vcAxioms;
        private readonly CFGRepr cfg;

        private readonly BasicCmdIsaVisitor basicCmdIsaVisitor = new BasicCmdIsaVisitor();
        private readonly PureValueIsaTransformer pureValueIsaTransformer = new PureValueIsaTransformer();
        private readonly PureTyIsaTransformer pureTyIsaTransformer = new PureTyIsaTransformer();

        private IDictionary<Axiom, int> axiomIdDict = null;

        private IEnumerable<Variable> ProgramVariables
        {
            get
            {
                return parameters.Union(localVars);
            }
        }

        private readonly IList<LemmaDecl> membershipLemmas = new List<LemmaDecl>();

        private readonly TermIdent functionInterp = IsaCommonTerms.TermIdentFromName("\\<Gamma>");
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
            IEnumerable<Function> functions,
            IEnumerable<Axiom> axioms,
            IEnumerable<Variable> parameters,
            IEnumerable<Variable> localVars,
            IsaProgramRepr isaProgramRepr,
            VCInstantiation<Block> vcinst,
            VCInstantiation<Axiom> vcinstAxiom,
            CFGRepr cfg)
        {
            this.functions = functions;
            this.axioms = axioms;
            this.parameters = parameters;
            this.localVars = localVars;
            this.isaProgramRepr = isaProgramRepr;
            this.vcinst = vcinst;
            this.vcinstAxiom = vcinstAxiom;
            this.cfg = cfg;
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
            AddMembershipLemmas(functions,
                isaProgramRepr.funcsDeclDef,
                d => IsaBoogieTerm.FunDecl((Function)d, false));
            //variables
            AddMembershipLemmas(parameters,
                isaProgramRepr.paramsDeclDef,
                d => IsaBoogieTerm.VarDecl((Variable)d, false));
            AddMembershipLemmas(localVars,
                isaProgramRepr.localVarsDeclDef,
                d => IsaBoogieTerm.VarDecl((Variable)d, false));
            AddAxiomMembershipLemmas();
        }

        private void AddMembershipLemmas(
            IEnumerable<NamedDeclaration> decls,
            Term declsDef,
            Func<NamedDeclaration, Term> declOf)
        {
            foreach (var d in decls)
            {
                Term lhs = new TermApp(
                    IsaCommonTerms.TermIdentFromName("map_of"),
                    new List<Term> { declsDef, new StringConst(d.Name) });
                Term rhs = IsaCommonTerms.SomeOption(declOf(d));

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
            Term axiomSat = IsaBoogieTerm.AxiomSat(funContext, isaProgramRepr.axiomsDeclDef, normalInitState);
            int id = 0;
            foreach (var axiom in axioms)
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
            return BasicUtil.ApplyFunDict(functions, VCFunDefinition);
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
            return BasicUtil.ApplyFunDict(functions, FunCorres);
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

            Term assm = IsaBoogieTerm.FunInterpSingleWf(IsaBoogieTerm.FunDecl(f, false), funTerm);

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
            var declToVCMapping = LemmaHelper.DeclToTerm(((IEnumerable<NamedDeclaration>)functions).Union(ProgramVariables), uniqueNamer);
            Term vcAssmWithoutAxioms = vcinst.GetVCObjInstantiation(cfg.entry, declToVCMapping);

            Term vcAssm =
                axioms.Aggregate(vcAssmWithoutAxioms, (vcCur, ax) =>
                    new TermBinary(vcinstAxiom.GetVCObjInstantiation(ax, declToVCMapping), vcCur, TermBinary.BinaryOpCode.META_IMP)
                );

            List<Identifier> declIds = declToVCMapping.Values.Select(t => t.id).ToList();
            List<TypeIsa> declTypes = functions.Select(f => pureTyIsaTransformer.Translate(f)).ToList();
            declTypes.AddRange(ProgramVariables.Select(v => pureTyIsaTransformer.Translate(v)));
            vcAssm = TermQuantifier.MetaAll(declIds, declTypes, vcAssm);

            Term funContext = new TermTuple(new List<Term> { isaProgramRepr.funcsDeclDef, functionInterp });

            Term finterpAssm = IsaBoogieTerm.FunInterpWf(isaProgramRepr.funcsDeclDef, functionInterp);
            Term axiomAssm = IsaBoogieTerm.AxiomSat(funContext, isaProgramRepr.axiomsDeclDef, normalInitState);
            Term paramsAssm = IsaBoogieTerm.StateWf(isaProgramRepr.paramsDeclDef, normalInitState);
            Term localVarsAssm = IsaBoogieTerm.StateWf(isaProgramRepr.localVarsDeclDef, normalInitState);
            Term multiRed = IsaBoogieTerm.RedCFGMulti(
                IsaCommonTerms.AppendList(isaProgramRepr.paramsDeclDef, isaProgramRepr.localVarsDeclDef),
                new TermTuple(new List<Term> { isaProgramRepr.funcsDeclDef, functionInterp }),
                isaProgramRepr.cfgDeclDef,
                IsaBoogieTerm.CFGConfigNode(new NatConst(cfg.GetUniqueIntLabel(cfg.entry)), IsaBoogieTerm.Normal(normalInitState)),
                IsaBoogieTerm.CFGConfig(finalNode, finalState)
                );

            Term conclusion = new TermBinary(finalState, IsaBoogieTerm.Failure(), TermBinary.BinaryOpCode.NEQ);

            var contextElem = ContextElem.CreateWithAssumptions(
                new List<Term> { vcAssm, finterpAssm, axiomAssm, paramsAssm, localVarsAssm, multiRed },
                new List<string> { vcAssmName, finterpAssmName, axiomAssmName, paramsAssmName, localVarsAssmName, RedAssmName });
            return new LemmaDecl("endToEnd", contextElem, conclusion, FinalProof());
        }

        private Proof FinalProof()
        {
            var sb = new StringBuilder();
            sb.AppendLine("proof -");

            //functions
            foreach(Function f in functions)
            {
                Term fStringConst = new StringConst(f.Name);
                sb.Append("let " + FunAbbrev(f) + " = ");
                sb.AppendInner("opaque_comp the " + functionInterp + " " + fStringConst);
                sb.AppendLine();
                sb.Append("from " + finterpAssmName + " have " + InterpMemName(f) + ":");
                sb.AppendInner(
                new TermBinary(new TermApp(functionInterp, fStringConst), 
                    IsaCommonTerms.SomeOption(IsaCommonTerms.TermIdentFromName(FunAbbrev(f))),
                    TermBinary.BinaryOpCode.EQ).ToString());
                sb.AppendLine();
                sb.AppendLine("apply " + ProofUtil.SimpOnly("opaque_comp_def"));
                sb.AppendLine("using " + "fun_interp_wf_def " + MembershipName(f) + " option.sel by metis");

                sb.Append("from " + finterpAssmName + " have " + WfName(f) + ":");
                sb.AppendInner(IsaBoogieTerm.FunInterpSingleWf(f, IsaCommonTerms.TermIdentFromName(FunAbbrev(f))).ToString());
                sb.AppendLine();
                sb.AppendLine("apply " + ProofUtil.SimpOnly("opaque_comp_def"));
                sb.AppendLine("using " + "fun_interp_wf_def " + MembershipName(f) + " option.sel by metis");
                sb.AppendLine();
            }

            //variables
            AppendStateCorres(sb, paramsAssmName, parameters);
            AppendStateCorres(sb, localVarsAssmName, localVars);

            //axioms
            Term funContext = new TermTuple(new List<Term> { isaProgramRepr.funcsDeclDef, functionInterp });

            foreach(Axiom ax in axioms)
            {
                Term axiomTerm = basicCmdIsaVisitor.Translate(ax.Expr);
                Term exprEvaluatesToTrue = IsaBoogieTerm.RedExpr(funContext, axiomTerm, normalInitState, IsaBoogieTerm.BoolVal(true));
                sb.Append("have "+ EvaluationName(ax) + ":" + " ");
                sb.AppendInner(exprEvaluatesToTrue.ToString()); sb.AppendLine();
                sb.AppendLine("by (rule axioms_sat_mem[OF " + MembershipName(ax) + " " + axiomAssmName +"])");
            }
            sb.AppendLine();

            //store function theorems
            sb.AppendLine("ML_prf \\<open>");
            sb.AppendLine();
            foreach(Function f in functions)
            {
                sb.AppendLine("val " + FunCorresName(f, true) + " = " + "@{thm " + ProofUtil.OF(FunCorresName(f), WfName(f)) + "}");
                sb.AppendLine("val " + InterpMemName(f, true) + " = " + "@{thm " + InterpMemName(f) + "}");
            }
            sb.AppendLine("\\<close>");

            //conclusion
            sb.Append("show ");
            sb.AppendInner(new TermBinary(finalState, IsaBoogieTerm.Failure(), TermBinary.BinaryOpCode.NEQ).ToString());
            sb.AppendLine();
     
            sb.AppendLine("apply (rule passification.method_verifies[OF _ " + RedAssmName + "])");
            sb.AppendLine("apply " + ProofUtil.SimpOnly("passification_def"));

            foreach(Function f in functions)
            {
                //TODO: Can be more precise with conjI tactic instead of using +, ?;
                //TODO: Use stored ML theorems to avoid re-instantiation
                sb.AppendLine("apply ((rule conjI)+, " + ProofUtil.Simp(InterpMemName(f)) + ", (rule conjI)?, " + 
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

            string interpLemmasList = "[" + IsaPrettyPrinterHelper.CommaAggregate(functions.Select(f => FunCorresName(f, true))) + ", " +
                IsaPrettyPrinterHelper.CommaAggregate(functions.Select(f => InterpMemName(f, true))) + "]";

            foreach(Axiom ax in axioms)
            {
                sb.AppendLine("apply " + ProofUtil.SimpOnly(vcinstAxiom.GetVCObjNameRef(ax) + "_def"));
                sb.AppendLine("apply (rule expr_to_vc[OF " + EvaluationName(ax) + "])");               
                sb.AppendLine("apply(tactic \\<open> b_vc_expr_rel_tac @{context} " + interpLemmasList + " [] 1 \\<close>)");
            }
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
                            v.TypedIdent.Type)
                            , v.TypedIdent.Type)
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
