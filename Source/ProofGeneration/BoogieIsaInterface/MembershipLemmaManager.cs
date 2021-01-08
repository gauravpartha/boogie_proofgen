using System;
using System.Collections.Generic;
using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface.VariableTranslation;
using ProofGeneration.Isa;
using ProofGeneration.ProgramToVCProof;
using ProofGeneration.Util;

namespace ProofGeneration.BoogieIsaInterface
{
    public class MembershipLemmaManager : IProgramAccessor
    {
        //defer calls to parent, which are not handled here
        private readonly IProgramAccessor parent;

        private readonly IVariableTranslationFactory factory;
        private readonly TypeIsaVisitor typeIsaVisitor;
        private readonly IsaProgramRepr isaProgramRepr;
        private readonly BasicCmdIsaVisitor basicCmdIsaVisitor;

        /*
        private bool containsFunctions = false;
        private bool containsAxioms = false;
        */

        private readonly string theoryName;

        private readonly IDictionary<Declaration, LemmaDecl> membershipLemmas = new Dictionary<Declaration, LemmaDecl>();
        private readonly IDictionary<Variable, LemmaDecl> lookupVarTyLemmas = new Dictionary<Variable, LemmaDecl>();
        private readonly List<LemmaDecl> helperLemmas = new List<LemmaDecl>();
        
        private readonly string[] paramsAndLocalsDefs;
        private readonly string[] constsAndGlobalsDefs;

        private readonly string consts;
        private readonly string globals;

        private readonly Term paramsAndLocalsList;
        private readonly Term constsAndGlobalsList;
        
        private readonly IsaUniqueNamer membershipNamer = new IsaUniqueNamer();
        private readonly IsaUniqueNamer lookupVarTyNamer = new IsaUniqueNamer();

        private readonly string localsMinName = "locals_min";
        private readonly string globalsMaxName = "globals_max";
        
        private readonly string globalsLocalsDisjName = "globals_locals_disj";

        private readonly IsaProgramGeneratorConfig config;
        private readonly IsaBlockInfo isaBlockInfo;
        
        public MembershipLemmaManager(
            IsaProgramGeneratorConfig config,
            IsaProgramRepr isaProgramRepr,
            IsaBlockInfo isaBlockInfo,
            Tuple<int, int> GlobalsMaxLocalsMin,
            IVariableTranslationFactory factory,
            string theoryName
        )
        {
            this.parent = config.ParentAccessor;
            this.isaProgramRepr = isaProgramRepr;
            this.factory = factory;
            this.theoryName = theoryName;
            this.config = config;
            this.isaBlockInfo = isaBlockInfo;
            typeIsaVisitor = new TypeIsaVisitor(factory.CreateTranslation().TypeVarTranslation);
            basicCmdIsaVisitor = new BasicCmdIsaVisitor(factory);
            paramsAndLocalsDefs =
                new string[] {isaProgramRepr.paramsDeclDef + "_def", isaProgramRepr.localVarsDeclDef + "_def"};

            paramsAndLocalsList =
                IsaCommonTerms.AppendList(IsaCommonTerms.TermIdentFromName(QualifyAccessName(isaProgramRepr.paramsDeclDef)),
                                        IsaCommonTerms.TermIdentFromName(QualifyAccessName(isaProgramRepr.localVarsDeclDef)));
            consts = config.GenerateConstants ? QualifyAccessName(isaProgramRepr.constantsDeclDef) : parent.ConstsDecl();
            globals = config.GenerateGlobals ? QualifyAccessName(isaProgramRepr.globalsDeclDef) : parent.GlobalsDecl(); 
            
            constsAndGlobalsDefs =
                new string[] {consts+ "_def", globals+ "_def"};
            constsAndGlobalsList =
                IsaCommonTerms.AppendList(IsaCommonTerms.TermIdentFromName(consts),
                    IsaCommonTerms.TermIdentFromName(globals));
            AddDisjointnessLemmas(GlobalsMaxLocalsMin.Item1, GlobalsMaxLocalsMin.Item2);
        }
        
        public string TheoryName()
        {
            return theoryName;
        }

        public Term FunctionsDecl()
        {
            if (config.GenerateFunctions)
                return QualifyAccessTerm(isaProgramRepr.funcsDeclDef);
                
            return parent.FunctionsDecl();
        }

        public Term AxiomsDecl()
        {
            if (config.GenerateAxioms)
                return QualifyAccessTerm(isaProgramRepr.axiomsDeclDef);
                
            return parent.AxiomsDecl();
        }

        public Term PreconditionsDecl()
        {
            if (config.GenerateSpecs)
                return QualifyAccessTerm(isaProgramRepr.preconditionsDeclDef);

            return parent.PreconditionsDecl();
        }

        public string PreconditionsDeclName()
        {
            if (config.GenerateSpecs)
                return QualifyAccessName(isaProgramRepr.preconditionsDeclDef);

            return parent.PreconditionsDeclName();
        }

        public Term PostconditionsDecl()
        {
            if (config.GenerateSpecs)
                return QualifyAccessTerm(isaProgramRepr.postconditionsDeclDef);

            return parent.PostconditionsDecl();
        }

        public string PostconditionsDeclName()
        {
            if (config.GenerateSpecs)
                return QualifyAccessName(isaProgramRepr.postconditionsDeclDef);

            return parent.PostconditionsDeclName();
        }
        
        public Term CfgDecl()
        {
            return QualifyAccessTerm(isaProgramRepr.cfgDeclDef);
        }

        public Term ParamsAndLocalsDecl()
        {
            return IsaCommonTerms.AppendList(QualifyAccessTerm(isaProgramRepr.paramsDeclDef), QualifyAccessTerm(isaProgramRepr.localVarsDeclDef));
        }

        public string ParamsDecl()
        {
            return QualifyAccessName(isaProgramRepr.paramsDeclDef);
        }

        public string LocalsDecl()
        {
            return QualifyAccessName(isaProgramRepr.localVarsDeclDef);
        }

        public Term ConstsAndGlobalsDecl()
        {
            return constsAndGlobalsList;
        }

        public string ConstsDecl()
        {
            return consts;
        }

        public string GlobalsDecl()
        {
            return globals;
        }
        
        private Term QualifyAccessTerm(string name)
        {
            return IsaCommonTerms.TermIdentFromName(QualifyAccessName(name));
        }

        private string QualifyAccessName(string name)
        {
            return theoryName + "." + name;
        }
        public string MembershipLemma(Declaration d)
        {
            /* for variables we don't have a fine-grained distinction (which would require knowing whether the variable is
             * global or not) --> TODO use subtype to distinguish */
            if (d is Variable && membershipLemmas.TryGetValue(d, out LemmaDecl result))
                return QualifyAccessName(result.name);
            
            if (d is Function && config.GenerateFunctions)
                return QualifyAccessName(membershipLemmas[d].name);

            if (d is Axiom && config.GenerateAxioms)
                return QualifyAccessName(membershipLemmas[d].name);
                
            return parent.MembershipLemma(d);
        }

        public IsaBlockInfo BlockInfo()
        {
            return isaBlockInfo;
        }

        public string LookupVarTyLemma(Variable v)
        {
            if (lookupVarTyLemmas.TryGetValue(v, out LemmaDecl result))
                return QualifyAccessName(result.name);

            return parent.LookupVarTyLemma(v);
        }

        public IEnumerable<OuterDecl> OuterDecls()
        {
            var result = new List<OuterDecl>();
            result.AddRange(helperLemmas);
            result.AddRange(membershipLemmas.Values);
            result.AddRange(lookupVarTyLemmas.Values);
            return result;
        }

        public void AddFunctionMembershipLemmas(IEnumerable<Function> functions)
        {
            AddNamedDeclsMembershipLemmas(functions,
                IsaCommonTerms.TermIdentFromName(isaProgramRepr.funcsDeclDef),
                new[] { isaProgramRepr.funcsDeclDef + "_def" },
                d => new StringConst(d.Name),
                d => IsaBoogieTerm.FunDecl((Function)d, factory, false),
                true 
                );
        }

        public void AddVariableMembershipLemmas(IEnumerable<Variable> variables, bool global, bool generateMembershipLemmas)
        {
            var varTranslation = factory.CreateTranslation().VarTranslation;
            Func<NamedDeclaration, Term> idOfVar =
                d =>
                {
                    if (varTranslation.TryTranslateVariableId((Variable) d, out Term varId, out bool isBoundVar) &&
                        !isBoundVar)
                    {
                        return varId;
                    }
                    else
                    {
                        throw new ProofGenUnexpectedStateException(typeof(EndToEndVCProof),
                            "Could not retrieve variable id");
                    }
                };

            Func<Variable, string> membershipLemmaLookup;
            if (generateMembershipLemmas)
            {
                AddNamedDeclsMembershipLemmas(variables,
                    global ? constsAndGlobalsList : paramsAndLocalsList,
                    global ? constsAndGlobalsDefs : paramsAndLocalsDefs,
                    idOfVar,
                    d => IsaBoogieTerm.VarDecl((Variable) d, typeIsaVisitor, false),
                    true);
                membershipLemmaLookup = v => membershipLemmas[v].name;
            }
            else
            {
                membershipLemmaLookup = v => parent.MembershipLemma(v);
            }

            //must come after adding membership lemmas (lemmas are looked up)
            AddLookupVarTyLemmas(variables, 
                idOfVar, 
                d => IsaBoogieTerm.VarDecl((Variable) d, typeIsaVisitor, false),
                membershipLemmaLookup
                );
        }

        private void AddNamedDeclsMembershipLemmas(
            IEnumerable<NamedDeclaration> decls,
            Term sourceList,
            string [] definitions,
            Func<NamedDeclaration, Term> nameOf,
            Func<NamedDeclaration, Term> declOf,
            bool useMapOf)
        {
            foreach (var d in decls)
            {
                Term lhs = new TermApp(
                    useMapOf ? IsaCommonTerms.TermIdentFromName("map_of") : IsaCommonTerms.TermIdentFromName("nth"),
                    new List<Term> { sourceList, nameOf(d) });
                Term rhs = useMapOf ? IsaCommonTerms.SomeOption(declOf(d)) : declOf(d);

                Term statement = TermBinary.Eq(lhs, rhs);
                Proof proof = new Proof(new List<string> { "by " + ProofUtil.Simp(definitions) });
                membershipLemmas.Add(d, new LemmaDecl(MembershipName(d), statement, proof));
            }
        }

        private void AddLookupVarTyLemmas(
            IEnumerable<Variable> vars, 
            Func<NamedDeclaration, Term> nameOf,
            Func<NamedDeclaration, Term> declOf,
            Func<Variable, string> getMembershipLemma)
        {
            foreach (var v in vars)
            {
                Term lhs = IsaBoogieTerm.LookupVarTy(VarContext(), nameOf(v));
                Term rhs = IsaCommonTerms.SomeOption(declOf(v));
                Term statement = TermBinary.Eq(lhs, rhs);
                Proof proof =
                    new Proof(new List<string>
                    {
                        "using " + globalsLocalsDisjName + " " + getMembershipLemma(v),
                        "by (simp add: lookup_var_ty_global_2 lookup_var_ty_local)"
                    });
                lookupVarTyLemmas.Add(v, new LemmaDecl(lookupVarTyNamer.GetName(v, "l_"+v.Name), statement, proof));
            }
        }

        public Term VarContext()
        {
            return new TermTuple(constsAndGlobalsList, paramsAndLocalsList);
        }
        
        public void AddAxiomMembershipLemmas(IEnumerable<Axiom> axioms)
        {
            Term axiomSet = IsaCommonTerms.SetOfList(IsaCommonTerms.TermIdentFromName(isaProgramRepr.axiomsDeclDef));
            int id = 0;
            foreach (var axiom in axioms)
            {
                Term axiomTerm = basicCmdIsaVisitor.Translate(axiom.Expr);
                Term elemAssm = IsaCommonTerms.Elem(axiomTerm, axiomSet);

                Proof proof = new Proof(new List<string> { "by (simp add: " + isaProgramRepr.axiomsDeclDef + "_def)" });
                membershipLemmas.Add(axiom, new LemmaDecl(MembershipName(axiom, id), elemAssm, proof));
                id++;
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

        private string MembershipName(Axiom a, int id)
        {
            return "ma_" + id;
        }

        public string GlobalsLocalsDisjointLemma()
        {
            return QualifyAccessName(globalsLocalsDisjName);
        }

        public string GlobalsAtMostMax()
        {
            if (config.GenerateGlobals)
                return QualifyAccessName(globalsMaxName);
            return parent.GlobalsAtMostMax();
        }
        
        public string LocalsAtLeastMin()
        {
            return QualifyAccessName(localsMinName);
        }

        private void AddMinOrMaxLemma(bool isGlobal, int bound, Term varNames)
        {
            var xId = new SimpleIdentifier("x");
            var x = new TermIdent(xId);
            var boundHelperLemma = 
                new LemmaDecl((isGlobal ? globalsMaxName : localsMinName) + "_aux",
                    TermBinary.Implies(
                       TermBinary.Neq(varNames, IsaCommonTerms.EmptyList),  
                       TermBinary.Eq(isGlobal ? 
                           IsaCommonTerms.SetMax(IsaCommonTerms.SetOfList(varNames)) : 
                           IsaCommonTerms.SetMin(IsaCommonTerms.SetOfList(varNames)), 
                           new NatConst(bound))
                        ), 
                    new Proof(new List<string>
                    {
                        "unfolding " + (isGlobal ? ConstsDecl() : ParamsDecl())+"_def " + (isGlobal ? GlobalsDecl() : LocalsDecl())+"_def",
                        "by simp"
                    })
                    );
            helperLemmas.Add(boundHelperLemma);
            
            var boundLemma = 
                new LemmaDecl(isGlobal ? globalsMaxName : localsMinName,
                    TermQuantifier.ForAll(
                        new List<Identifier> { xId },
                        null,
                        TermBinary.Implies(
                            IsaCommonTerms.Elem(x, IsaCommonTerms.SetOfList(varNames)),
                            new TermBinary(x, new NatConst(bound), isGlobal ? TermBinary.BinaryOpCode.LE : TermBinary.BinaryOpCode.GE)
                            )
                        ),
                    new Proof(new List<string>
                    {
                        "using " + boundHelperLemma.name,
                        "by (metis " + (isGlobal ? " helper_max list.map_disc_iff)" : " helper_min list.map_disc_iff)")
                    })
                    );
            
            helperLemmas.Add(boundLemma);
            
        }
        

        private void AddDisjointnessLemmas(int globalsMax, int localsMin)
        {
            var globalNames = VariableNames(constsAndGlobalsList);
            var localNames = VariableNames(paramsAndLocalsList);
            
            if (config.GenerateGlobals)
            {
                AddMinOrMaxLemma(true, globalsMax, globalNames);
            }
            
            AddMinOrMaxLemma(false, localsMin, localNames);

            Term statement = TermBinary.Eq(
                IsaCommonTerms.SetInter(IsaCommonTerms.SetOfList(globalNames), IsaCommonTerms.SetOfList(localNames)),
                IsaCommonTerms.EmptySet
            );

            List<string> proofMethods;
            if (globalsMax == localsMin)
            {
                //-> global set is empty
                proofMethods = new List<string>
                {
                    "unfolding " + ConstsDecl()+"_def " + GlobalsDecl() +"_def",
                    "by simp"
                };
            }
            else
            {
                proofMethods = new List<string>
                {
                    "using " + LocalsAtLeastMin() + " " + GlobalsAtMostMax(),
                    "by fastforce"
                };
            }
            helperLemmas.Add(
                new LemmaDecl(globalsLocalsDisjName, statement, new Proof(proofMethods))
            );
        }

        private Term VariableNames(Term variableDeclarations)
        {
            return IsaCommonTerms.Map(IsaCommonTerms.FstId, variableDeclarations);
        }

    }
}