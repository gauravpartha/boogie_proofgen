using System;
using System.Collections.Generic;
using System.Linq;
using Isabelle.Ast;
using Isabelle.Util;
using Microsoft.BaseTypes;
using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.BoogieIsaInterface.VariableTranslation;
using ProofGeneration.CFGRepresentation;
using ProofGeneration.Util;

namespace ProofGeneration
{
    public class IsaProgramGeneratorConfig
    {
        public readonly bool generateAxioms;
        public readonly bool generateFunctions;
        public readonly bool generateGlobalsAndConstants;
        public readonly bool generateParamsAndLocals;
        public readonly bool generateSpecs;
        public readonly bool generateVarContextWfLemma;
        public readonly IProgramAccessor parentAccessor;
        
        public IsaProgramGeneratorConfig(
            IProgramAccessor parent,
            bool generateFunctions,
            bool generateAxioms,
            bool generateGlobalsAndConstants,
            bool generateParamsAndLocals,
            bool generateSpecs,
            bool generateVarContextWfLemma
        )
        {
            parentAccessor = parent;
            this.generateFunctions = generateFunctions;
            this.generateAxioms = generateAxioms;
            this.generateSpecs = generateSpecs;
            this.generateGlobalsAndConstants = generateGlobalsAndConstants;
            this.generateParamsAndLocals = generateParamsAndLocals;
            this.generateVarContextWfLemma = generateVarContextWfLemma;
        }
    }

    internal class IsaProgramGenerator
    {
        private MultiCmdIsaVisitor cmdIsaVisitor;
        private BoogieVariableTranslation varTranslation;
        private IVariableTranslationFactory varTranslationFactory;
        
        private readonly string nodeToBlocksName = "node_to_blocks";
        private readonly string cfgName = "method_body";

        public IProgramAccessor GetIsaProgram(
            string theoryName,
            string procName,
            BoogieMethodData methodData,
            IsaProgramGeneratorConfig config,
            IVariableTranslationFactory varTranslationFactory,
            CFGRepr cfg,
            out IList<OuterDecl> decls,
            bool generateMembershipLemmas = true,
            bool onlyGlobalData = false
        )
        {
            this.varTranslationFactory = varTranslationFactory;
            varTranslation = varTranslationFactory.CreateTranslation();
            cmdIsaVisitor = new MultiCmdIsaVisitor(varTranslationFactory);

            /*
            Term method = IsaBoogieTerm.Method(
                procName, 
                methodData.TypeParams.Count(), 
                IsaCommonTerms.TermIdentFromName(parameters.name), 
                IsaCommonTerms.TermIdentFromName(localVariables.name), 
                modifiedVariables,
                IsaCommonTerms.TermIdentFromName(preconditions.name),
                IsaCommonTerms.TermIdentFromName(postconditions.name),
                IsaCommonTerms.TermIdentFromName(methodBodyDecl.name)
                    );
            */
            /*
            Term program = IsaBoogieTerm.Program(IsaCommonTerms.TermIdentFromName(funcs.name),
                new TermList(new List<Term>()),
                new TermList(new List<Term>()),
                IsaCommonTerms.TermIdentFromName(axiomsDecl.name),
                new List<Term>() { method });

            var list = new List<Tuple<IList<Term>, Term>>
            {
                new Tuple<IList<Term>, Term>(new List<Term>(), program)
            };
            */

            //OuterDecl programDefinition = new DefDecl("ProgramM", new Tuple<IList<Term>, Term>(new List<Term>(), program));

            decls = new List<OuterDecl>();
            var isaGlobalProgramRepr = new IsaGlobalProgramRepr(
                FunctionDeclarationsName(),
                AxiomDeclarationsName(),
                VariableDeclarationsName("globals"),
                VariableDeclarationsName("constants")
                );
            var globalsMax = methodData.Constants.Count() + methodData.GlobalVars.Count() - 1;
            // assume single versioning and order on constants, globals, params, locals
            var localsMin = globalsMax + 1;
            if (globalsMax < 0)
                globalsMax = 0;

            MembershipLemmaManager membershipLemmaManager;
            if (onlyGlobalData)
            {
                membershipLemmaManager = new MembershipLemmaManager(
                        isaGlobalProgramRepr, globalsMax, varTranslationFactory, theoryName );
            }
            else
            {
                var outEdges = GetOutEdgesIsa(procName, cfg, out var edgeLemmas);
                var blockInfo = BlockToInfo(theoryName, procName, cfg, edgeLemmas);
                var isaProgramRepr = new IsaProgramRepr(
                    isaGlobalProgramRepr,
                    PreconditionDeclarationName(procName),
                    PostconditionDeclarationName(procName),
                    VariableDeclarationsName("params"),
                    VariableDeclarationsName("locals"),
                    cfgName);
                membershipLemmaManager = new MembershipLemmaManager(config, isaProgramRepr, blockInfo,
                Tuple.Create(globalsMax, localsMin), varTranslationFactory, theoryName);
                
                var nodesToBlocks = GetNodeToBlocksIsa(cfg, blockInfo.BlockCmdsDefs);

                decls.AddRange(blockInfo.BlockCmdsDefs.Values);
                
                Term entry = new IntConst(BigNum.FromInt(cfg.GetUniqueIntLabel(cfg.entry)));
                var methodBodyCFG =
                    IsaBoogieTerm.MethodCFGBody(
                        entry, IsaCommonTerms.TermIdentFromName(outEdges.Name),
                        IsaCommonTerms.TermIdentFromName(nodesToBlocks.Name)
                    );

                var methodBodyDecl = GetMethodBodyCFGDecl(procName, methodBodyCFG);
                decls.AddRange(
                    new List<OuterDecl>
                    {
                        outEdges, nodesToBlocks, methodBodyDecl
                    });

                decls.AddRange(blockInfo.BlockCmdsLemmas.Values);
                decls.AddRange(blockInfo.BlockOutEdgesLemmas.Values);
                
                if (config.generateSpecs)
                {
                    OuterDecl preconditions =
                        GetExprListIsa(PreconditionDeclarationName(procName), methodData.Preconditions);
                    OuterDecl postconditions =
                        GetExprListIsa(PostconditionDeclarationName(procName), methodData.Postconditions);
                    decls.Add(preconditions);
                    decls.Add(postconditions);
                }

                if(config.generateParamsAndLocals) {
                    decls.Add(GetVariableDeclarationsIsa("params", methodData.InParams));
                    decls.Add(GetVariableDeclarationsIsa("locals", methodData.Locals));
                }
                
                /* membership lemmas might still be added even if the parameter and local variable definitions are not generated
                 * at this point (since the variable context may still be different, which requires other lookup lemmas)
                 */
                if (generateMembershipLemmas)
                {
                    membershipLemmaManager.AddVariableMembershipLemmas(methodData.InParams, VarKind.ParamOrLocal);
                    membershipLemmaManager.AddVariableMembershipLemmas(methodData.Locals, VarKind.ParamOrLocal);
                }
            }

            if (config.generateAxioms)
            {
                decls.Add(GetAxioms(methodData.Axioms));
                if(generateMembershipLemmas) membershipLemmaManager.AddAxiomMembershipLemmas(methodData.Axioms);
            }

            if (config.generateFunctions)
            {
                decls.Add(GetFunctionDeclarationsIsa(methodData.Functions));
                if(generateMembershipLemmas) membershipLemmaManager.AddFunctionMembershipLemmas(methodData.Functions);
            }

            if (config.generateGlobalsAndConstants)
            {
                decls.Add(GetVariableDeclarationsIsa("globals", methodData.GlobalVars));
                decls.Add(GetVariableDeclarationsIsa("constants", methodData.Constants));
            }

            if (generateMembershipLemmas)
            {
                membershipLemmaManager.AddVariableMembershipLemmas(methodData.GlobalVars, VarKind.Global);
                membershipLemmaManager.AddVariableMembershipLemmas(methodData.Constants, VarKind.Constant);
                decls.AddRange(membershipLemmaManager.OuterDecls());
            }

            return membershipLemmaManager;
        }

        private DefDecl GetAxioms(IEnumerable<Axiom> axioms)
        {
            var axiomsExpr = new List<Term>();
            foreach (var ax in axioms)
            {
                var axTerms = cmdIsaVisitor.Translate(ax.Expr);
                if (axTerms.Count != 1)
                    throw new ProofGenUnexpectedStateException(GetType(), "axiom not translated into single term");
                axiomsExpr.Add(axTerms.First());
            }

            var equation = new Tuple<IList<Term>, Term>(new List<Term>(), new TermList(axiomsExpr));

            return new DefDecl(AxiomDeclarationsName(), equation);
        }

        private string AxiomDeclarationsName()
        {
            return "axioms";
        }

        private IsaBlockInfo BlockToInfo(string theoryName, string methodName, CFGRepr cfg,
            Dictionary<Block, LemmaDecl> edgeLemmas)
        {
            //TODO: redundant to have extra indexing map, re-use labelling map
            var blockToCounter = new Dictionary<Block, int>();
            var blockToDecl = new Dictionary<Block, OuterDecl>();
            var blockToNodesLemmas = new Dictionary<Block, LemmaDecl>();

            var cfgTerm = IsaCommonTerms.TermIdentFromName(cfgName);
            var cfgDef = cfgName + "_def";
            var nodeToBlockDef = nodeToBlocksName + "_def";

            foreach (var b in cfg.GetBlocksBackwards())
            {
                //left side of equation is block number expressed using constructors
                //right side of equation is command
                var translatedBlocks = cmdIsaVisitor.Translate(b.Cmds);
                var blockDecl = DefDecl.CreateWithoutArg("block_" + cfg.GetUniqueIntLabel(b),
                    new TermList(translatedBlocks));
                blockToDecl.Add(b, blockDecl);

                var blockLabel = cfg.GetUniqueIntLabel(b);

                // nodes lemma
                {
                    var nodeDecl = new LemmaDecl(
                        NodeLemmaName(blockLabel),
                        ContextElem.CreateEmptyContext(),
                        TermBinary.Eq(IsaBoogieTerm.NodeToBlock(cfgTerm, blockLabel),
                            IsaCommonTerms.TermIdentFromName(blockDecl.Name)),
                        new Proof(new List<string> {"by " + ProofUtil.Simp(cfgDef, nodeToBlockDef)}));

                    blockToNodesLemmas.Add(b, nodeDecl);
                }
                blockToCounter[b] = blockLabel;
            }

            return new IsaBlockInfo(theoryName, blockToCounter, blockToDecl, edgeLemmas, blockToNodesLemmas);
        }

        private OuterDecl GetOutEdgesIsa(string methodName, CFGRepr cfg, out Dictionary<Block, LemmaDecl> edgeLemmas)
        {
            //var equations = new List<Tuple<IList<Term>, Term>>();
            var edgeList = new List<Term>();
            edgeLemmas = new Dictionary<Block, LemmaDecl>();

            var cfgTerm = IsaCommonTerms.TermIdentFromName(cfgName);
            var cfgDef = cfgName + "_def";
            string outEdgesDefName = "outEdges";
            var outEdgesDef = outEdgesDefName + "_def";

            foreach (var b in cfg.GetBlocksBackwards())
            {
                var outgoing = cfg.GetSuccessorBlocks(b);
                Term edges = new TermList(outgoing.Select(b_succ => (Term) new NatConst(cfg.GetUniqueIntLabel(b_succ)))
                    .ToList());
                edgeList.Add(edges);
                // edges lemma

                var blockLabel = cfg.GetUniqueIntLabel(b);
                var edgeDecl = new LemmaDecl(OutEdgesLemmaName(blockLabel),
                    ContextElem.CreateEmptyContext(),
                    TermBinary.Eq(IsaBoogieTerm.OutEdges(cfgTerm, blockLabel), edges),
                    new Proof(new List<string> {"by " + ProofUtil.Simp(cfgDef, outEdgesDef)}));

                edgeLemmas.Add(b, edgeDecl);
            }

            //empty set for remaining cases
            return DefDecl.CreateWithoutArg(outEdgesDefName, new TermList(edgeList));
        }

        private string OutEdgesLemmaName(int blockId)
        {
            return "outEdges_" + blockId;
        }

        private string NodeLemmaName(int blockId)
        {
            return "node_" + blockId;
        }

        private OuterDecl GetNodeToBlocksIsa(CFGRepr cfg, IDictionary<Block, OuterDecl> blockToDecl)
        {
            var nodeList = new List<Term>();

            foreach (var b in cfg.GetBlocksBackwards())
                //left side of equation is block number expressed using constructors
                //right side of equation is command
                nodeList.Add(IsaCommonTerms.TermIdentFromName(blockToDecl[b].Name));

            return DefDecl.CreateWithoutArg(nodeToBlocksName, new TermList(nodeList));
        }

        private DefDecl GetFunctionDeclarationsIsa(IEnumerable<Function> functions)
        {
            //var equations = new List<Tuple<IList<Term>, Term>>();
            var fdecls = new List<Term>();


            foreach (var f in functions) fdecls.Add(IsaBoogieTerm.FunDecl(f, varTranslationFactory));

            return DefDecl.CreateWithoutArg(FunctionDeclarationsName(), new TermList(fdecls));
        }

        private string FunctionDeclarationsName()
        {
            return "fdecls";
        }

        private string PreconditionDeclarationName(string methodName)
        {
            return "pres";
        }

        private string PostconditionDeclarationName(string methodName)
        {
            return "post";
        }

        private DefDecl GetVariableDeclarationsIsa(string varKind, IEnumerable<Variable> variables)
        {
            var typeIsaVisitor = new TypeIsaVisitor(varTranslation.TypeVarTranslation);

            var vdecls = new List<Term>();

            foreach (var v in variables)
            {
                if (varTranslation.VarTranslation.TryTranslateVariableId(v, out var resId, out _))
                {
                    vdecls.Add(IsaBoogieTerm.VarDecl(v, resId, typeIsaVisitor, cmdIsaVisitor.TranslateSingle));
                }
                else
                {
                    throw new ProofGenUnexpectedStateException(GetType(), "Cannot translate variable " + v.Name);
                }
            }

            var equation = new Tuple<IList<Term>, Term>(new List<Term>(), new TermList(vdecls));
            return new DefDecl(VariableDeclarationsName(varKind), IsaBoogieType.VariableDeclsType,
                equation);
        }

        private string VariableDeclarationsName(string varKind)
        {
            return varKind + "_vdecls";
        }

        private DefDecl GetExprListIsa(string declName, IEnumerable<Tuple<Expr,bool>> exprs)
        {
            var result = new List<Term>();
            foreach (var expr in exprs)
            {
                var termTuple = new TermTuple(cmdIsaVisitor.TranslateSingle(expr.Item1), new BoolConst(expr.Item2));
                result.Add(termTuple);
            }

            return DefDecl.CreateWithoutArg(declName, new TermList(result));
        }

        private DefDecl GetMethodBodyCFGDecl(string methodName, Term methodBodyCFG)
        {
            return DefDecl.CreateWithoutArg(cfgName, methodBodyCFG);
        }

    }
}