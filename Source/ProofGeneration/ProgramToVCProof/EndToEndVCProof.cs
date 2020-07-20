using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.CFGRepresentation;
using ProofGeneration.Isa;
using ProofGeneration.IsaPrettyPrint;
using ProofGeneration.Util;
using ProofGeneration.VCProofGen;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace ProofGeneration.ProgramToVCProof
{
    class EndToEndVCProof
    {
        private readonly IEnumerable<Function> functions;
        private readonly IEnumerable<Variable> parameters;
        private readonly IEnumerable<Variable> localVars;
        private readonly IsaProgramRepr isaProgramRepr;
        private readonly VCInstantiation vcinst;
        private readonly CFGRepr cfg;

        private readonly PureValueIsaTransformer pureValueIsaTransfomer = new PureValueIsaTransformer();
        private readonly PureTyIsaTransformer pureTyIsaTransfomer = new PureTyIsaTransformer();


        private IEnumerable<Variable> ProgramVariables
        {
            get
            {
                return localVars.Union(parameters);
            }
        }

        private readonly IDictionary<NamedDeclaration, LemmaDecl> membershipLemmasDict = new Dictionary<NamedDeclaration, LemmaDecl>();

        private readonly TermIdent functionInterp = IsaCommonTerms.TermIdentFromName("\\<Gamma>");
        private readonly TermIdent normalInitState = IsaCommonTerms.TermIdentFromName("n_s");
        private readonly TermIdent finalState = IsaCommonTerms.TermIdentFromName("s'");
        private readonly TermIdent finalNode = IsaCommonTerms.TermIdentFromName("m'");

        private readonly string vcAssmName = "VC";
        private readonly string finterpAssmName = "FInterp";
        private readonly string paramsAssmName = "Params";
        private readonly string localVarsAssmName = "LocalVars";
        private readonly string RedAssmName = "Red";

        public EndToEndVCProof(
            IEnumerable<Function> functions, 
            IEnumerable<Variable> parameters, 
            IEnumerable<Variable> localVars,
            IsaProgramRepr isaProgramRepr,
            VCInstantiation vcinst,
            CFGRepr cfg)
        {
            this.functions = functions;
            this.parameters = parameters;
            this.localVars = localVars;
            this.isaProgramRepr = isaProgramRepr;
            this.vcinst = vcinst;
            this.cfg = cfg;
        }

        public IEnumerable<OuterDecl> GenerateProof()
        {
            List<OuterDecl> result = new List<OuterDecl>();
            AddMembershipLemmas();

            result.AddRange(membershipLemmasDict.Values);
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
                membershipLemmasDict.Add(d, new LemmaDecl(MembershipName(d), statement, proof));
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

            IEnumerable<Term> paramsVal = paramsTerm.Select((p, idx) => pureValueIsaTransfomer.ConstructValue(p, f.InParams[idx].TypedIdent.Type));

            Term outputVal = IsaCommonTerms.TheOption(new TermApp(funTerm, new TermList(paramsVal.ToList())));
            Term pureOutputVal = pureValueIsaTransfomer.DestructValue(outputVal, f.OutParams[0].TypedIdent.Type);

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

            IEnumerable<Term> paramsVal = paramsTerm.Select((p, idx) => pureValueIsaTransfomer.ConstructValue(p, f.InParams[idx].TypedIdent.Type));

            Term vc_f = IsaCommonTerms.TermIdentFromName(VCFunName(f));

            Term assm = IsaBoogieTerm.FunInterpSingleWf(IsaBoogieTerm.FunDecl(f, false), funTerm);

            Term lhs = new TermApp(funTerm, new TermList(paramsVal.ToList()));
            Term rhs = IsaCommonTerms.SomeOption(pureValueIsaTransfomer.ConstructValue(new TermApp(vc_f, args), f.OutParams[0].TypedIdent.Type));
            Term innerStatement = new TermBinary(lhs, rhs, TermBinary.BinaryOpCode.EQ);

            var paramTypesIsa = f.InParams.Select(p => pureTyIsaTransfomer.Translate(p.TypedIdent.Type)).ToList();
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
            var vcAssm = vcinst.GetVCBlockInstantiation(cfg.entry, declToVCMapping);

            List<Identifier> declIds = declToVCMapping.Values.Select(t => t.id).ToList();
            List<TypeIsa> declTypes = functions.Select(f => pureTyIsaTransfomer.Translate(f)).ToList();
            declTypes.AddRange(ProgramVariables.Select(v => pureTyIsaTransfomer.Translate(v)));
            vcAssm = TermQuantifier.MetaAll(declIds, declTypes, vcAssm);

            Term finterpAssm = IsaBoogieTerm.FunInterpWf(isaProgramRepr.funcsDeclDef, functionInterp);
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
                new List<Term> { vcAssm, finterpAssm, paramsAssm, localVarsAssm, multiRed },
                new List<string> { vcAssmName, finterpAssmName, paramsAssmName, localVarsAssmName, RedAssmName });
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

            //conclusion
            sb.Append("show ");
            sb.AppendInner(new TermBinary(finalState, IsaBoogieTerm.Failure(), TermBinary.BinaryOpCode.NEQ).ToString());
            sb.AppendLine();
     
            sb.AppendLine("apply (rule passification.method_verifies[OF _ " + RedAssmName + "])");
            sb.AppendLine("apply " + ProofUtil.SimpOnly("passification_def"));

            foreach(Function f in functions)
            {
                //could be more precise with second conjI instead of using the optional tactical
                sb.AppendLine("apply (rule conjI, " + ProofUtil.Simp(InterpMemName(f)) + ", (rule conjI)?, " + 
                    "rule " + FunCorresName(f)+"[OF "+ WfName(f) +"])");
            }

            int numProgramVars = ProgramVariables.Count();
            int idx = 0;
            foreach(Variable v in ProgramVariables)
            {
                string conjIOpt = "";
                if(idx != numProgramVars-1)
                {
                    conjIOpt = "rule conjI, ";
                }
                idx++;

                sb.AppendLine("apply (" + conjIOpt + " rule " + StateCorresName(v)+ ")");
            }

            sb.AppendLine("by (rule " + vcAssmName + ")");
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
                    pureValueIsaTransfomer.ConstructValue(
                        pureValueIsaTransfomer.DestructValue(
                            IsaCommonTerms.TheOption(lhs),
                            v.TypedIdent.Type)
                            , v.TypedIdent.Type)
                        );
                sb.AppendInner(new TermBinary(lhs, rhs, TermBinary.BinaryOpCode.EQ).ToString());
                sb.AppendLine();
                sb.AppendLine("apply " + ProofUtil.SimpOnly("state_typ_wf_def"));
                sb.AppendLine("apply (erule allE, erule allE, erule impE, rule " + MembershipName(v) +")");
                sb.AppendLine("by (fastforce dest: tint_intv)");
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

        private string FunAbbrev(Function f)
        {
            return "?" + f.Name;
        }

        private string InterpMemName(Function f)
        {
            return "im_" + f.Name;
        }

        private string WfName(Function f)
        {
            return "i_" + f.Name;
        }

        private string FunCorresName(Function f)
        {
            return "vc_" + f.Name + "_corres";
        }

        private string StateCorresName(Variable v)
        {
            return "sc_" + v.Name;
        }

    }
}
