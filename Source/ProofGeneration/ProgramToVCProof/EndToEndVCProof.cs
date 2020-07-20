using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.Isa;
using ProofGeneration.IsaPrettyPrint;
using ProofGeneration.Util;
using ProofGeneration.VCProofGen;
using System;
using System.Collections.Generic;
using System.Linq;

namespace ProofGeneration.ProgramToVCProof
{
    class EndToEndVCProof
    {
        private readonly IEnumerable<Function> functions;
        private readonly IEnumerable<Variable> parameters;
        private readonly IEnumerable<Variable> localVars;
        private readonly IsaProgramRepr isaProgramRepr;
        private readonly VCInstantiation vcinst;
        private readonly Block entryBlock;

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

        private readonly string memPrefix = "mem";
        private int memId = 0;

        private readonly TermIdent functionInterp = IsaCommonTerms.TermIdentFromName("\\<Gamma>");
        private readonly TermIdent normalInitState = IsaCommonTerms.TermIdentFromName("n_s");
        private readonly TermIdent finalState = IsaCommonTerms.TermIdentFromName("s'");
        private readonly TermIdent finalNode = IsaCommonTerms.TermIdentFromName("m'");

        private readonly string vcAssmName = "VC";
        private readonly string finterpAssmName = "FInterp";
        private readonly string LocalVarsAssmName = "Params";
        private readonly string ParamsAssmName = "Params";
        private readonly string RedAssmNAme = "Red";

        public EndToEndVCProof(
            IEnumerable<Function> functions, 
            IEnumerable<Variable> parameters, 
            IEnumerable<Variable> localVars,
            IsaProgramRepr isaProgramRepr,
            VCInstantiation vcinst,
            Block entryBlock)
        {
            this.functions = functions;
            this.parameters = parameters;
            this.localVars = localVars;
            this.isaProgramRepr = isaProgramRepr;
            this.vcinst = vcinst;
            this.entryBlock = entryBlock;
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
                membershipLemmasDict.Add(d, new LemmaDecl(memPrefix + memId, statement, proof));
                memId++;
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

            return new LemmaDecl("vc_" + f.Name + "_corres", ContextElem.CreateWithAssumptions(assm), conclusion, new Proof(proofMethods));
        }

        public LemmaDecl FinalLemma()
        {
            var uniqueNamer = new IsaUniqueNamer();
            var declToVCMapping = LemmaHelper.DeclToTerm(((IEnumerable<NamedDeclaration>)functions).Union(ProgramVariables), uniqueNamer);
            var vcAssm = vcinst.GetVCBlockInstantiation(entryBlock, declToVCMapping);

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
                IsaBoogieTerm.CFGConfigNode(new NatConst(0), IsaBoogieTerm.Normal(normalInitState)),
                IsaBoogieTerm.CFGConfig(finalNode, finalState)
                );

            Term conclusion = new TermBinary(finalState, IsaBoogieTerm.Failure(), TermBinary.BinaryOpCode.NEQ);

            var contextElem = ContextElem.CreateWithAssumptions(new List<Term> { vcAssm, finterpAssm, paramsAssm, localVarsAssm, multiRed });
            return new LemmaDecl("endToEnd", contextElem, conclusion, new Proof(new List<string> { "oops" }));
        }


    }
}
