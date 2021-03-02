﻿using System;
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
        public bool GenerateAxioms;
        public bool GenerateFunctions;
        public bool GenerateGlobalsAndConstants;
        public bool GenerateParamsAndLocals;
        public bool GenerateSpecs;
        public IProgramAccessor ParentAccessor;

        public IsaProgramGeneratorConfig(
            IProgramAccessor parent,
            bool generateFunctions,
            bool generateAxioms,
            bool generateGlobalsAndConstants,
            bool generateParamsAndLocals,
            bool generateSpecs
        )
        {
            ParentAccessor = parent;
            GenerateFunctions = generateFunctions;
            GenerateAxioms = generateAxioms;
            GenerateSpecs = generateSpecs;
            GenerateGlobalsAndConstants = generateGlobalsAndConstants;
            GenerateParamsAndLocals = generateParamsAndLocals;
        }
    }

    internal class IsaProgramGenerator
    {
        private MultiCmdIsaVisitor cmdIsaVisitor;
        private BoogieVariableTranslation varTranslation;
        private IVariableTranslationFactory varTranslationFactory;

        public IProgramAccessor GetIsaProgram(
            string theoryName,
            string procName,
            BoogieMethodData methodData,
            IsaProgramGeneratorConfig config,
            IVariableTranslationFactory varTranslationFactory,
            CFGRepr cfg,
            out IList<OuterDecl> decls
        )
        {
            this.varTranslationFactory = varTranslationFactory;
            varTranslation = varTranslationFactory.CreateTranslation();
            cmdIsaVisitor = new MultiCmdIsaVisitor(varTranslationFactory);
            Term entry = new IntConst(BigNum.FromInt(cfg.GetUniqueIntLabel(cfg.entry)));

            var outEdges = GetOutEdgesIsa(procName, cfg, out var edgeLemmas);
            var blockInfo = BlockToInfo(theoryName, procName, cfg, edgeLemmas);
            var nodesToBlocks = GetNodeToBlocksIsa(procName, cfg, blockInfo.BlockCmdsDefs);

            //TermList modifiedVariables = new TermList(new List<Term>()); //TODO

            var methodBodyCFG =
                IsaBoogieTerm.MethodCFGBody(
                    entry, IsaCommonTerms.TermIdentFromName(outEdges.Name),
                    IsaCommonTerms.TermIdentFromName(nodesToBlocks.Name)
                );

            var methodBodyDecl = GetMethodBodyCFGDecl(procName, methodBodyCFG);

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
            decls.AddRange(blockInfo.BlockCmdsDefs.Values);
            var isaProgramRepr = new IsaProgramRepr(
                FunctionDeclarationsName(procName),
                AxiomDeclarationsName(procName),
                PreconditionDeclarationName(procName),
                PostconditionDeclarationName(procName),
                VariableDeclarationsName("globals", procName),
                VariableDeclarationsName("constants", procName),
                VariableDeclarationsName("params", procName),
                VariableDeclarationsName("locals", procName),
                methodBodyDecl.Name);
            // assume single versioning and order on constants, globals, params, locals
            var globalsMax = methodData.Constants.Count() + methodData.GlobalVars.Count() - 1;
            var localsMin = globalsMax + 1;
            if (globalsMax < 0)
                globalsMax = 0;
            var membershipLemmaManager = new MembershipLemmaManager(config, isaProgramRepr, blockInfo,
                Tuple.Create(globalsMax, localsMin), varTranslationFactory, theoryName);

            if (config.GenerateAxioms)
            {
                decls.Add(GetAxioms(procName, methodData.Axioms));
                membershipLemmaManager.AddAxiomMembershipLemmas(methodData.Axioms);
            }

            if (config.GenerateFunctions)
            {
                decls.Add(GetFunctionDeclarationsIsa(procName, methodData.Functions));
                membershipLemmaManager.AddFunctionMembershipLemmas(methodData.Functions);
            }

            if (config.GenerateSpecs)
            {
                OuterDecl preconditions =
                    GetExprListIsa(PreconditionDeclarationName(procName), methodData.Preconditions);
                OuterDecl postconditions =
                    GetExprListIsa(PostconditionDeclarationName(procName), methodData.Postconditions);
                decls.Add(preconditions);
                decls.Add(postconditions);
            }

            decls.Add(GetVariableDeclarationsIsa("globals", procName, methodData.GlobalVars));
            membershipLemmaManager.AddVariableMembershipLemmas(methodData.GlobalVars, VarKind.Global,
                config.GenerateGlobalsAndConstants);

            decls.Add(GetVariableDeclarationsIsa("constants", procName, methodData.Constants));
            membershipLemmaManager.AddVariableMembershipLemmas(methodData.Constants, VarKind.Constant,
                config.GenerateGlobalsAndConstants);

            decls.Add(GetVariableDeclarationsIsa("params", procName, methodData.InParams));
            membershipLemmaManager.AddVariableMembershipLemmas(methodData.InParams, VarKind.ParamOrLocal,
                config.GenerateParamsAndLocals);

            decls.Add(GetVariableDeclarationsIsa("locals", procName, methodData.Locals));
            membershipLemmaManager.AddVariableMembershipLemmas(methodData.Locals, VarKind.ParamOrLocal,
                config.GenerateParamsAndLocals);

            decls.AddRange(
                new List<OuterDecl>
                {
                    outEdges, nodesToBlocks, methodBodyDecl
                });

            decls.AddRange(blockInfo.BlockCmdsLemmas.Values);
            decls.AddRange(blockInfo.BlockOutEdgesLemmas.Values);
            decls.AddRange(membershipLemmaManager.OuterDecls());

            return membershipLemmaManager;
        }


        private DefDecl GetAxioms(string methodName, IEnumerable<Axiom> axioms)
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

            return new DefDecl(AxiomDeclarationsName(methodName), equation);
        }

        private string AxiomDeclarationsName(string methodName)
        {
            return "axioms_" + methodName;
        }

        private IsaBlockInfo BlockToInfo(string theoryName, string methodName, CFGRepr cfg,
            Dictionary<Block, LemmaDecl> edgeLemmas)
        {
            //TODO: redundant to have extra indexing map, re-use labelling map
            var blockToCounter = new Dictionary<Block, int>();
            var blockToDecl = new Dictionary<Block, OuterDecl>();
            var blockToNodesLemmas = new Dictionary<Block, LemmaDecl>();

            var cfgTerm = IsaCommonTerms.TermIdentFromName(CfgName(methodName));
            var cfgDef = CfgName(methodName) + "_def";
            var nodeToBlockDef = "nodeToBlocks_" + methodName + "_def";

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

            var cfgTerm = IsaCommonTerms.TermIdentFromName(CfgName(methodName));
            var cfgDef = CfgName(methodName) + "_def";
            var outEdgesDef = "outEdges_" + methodName + "_def";

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
            return DefDecl.CreateWithoutArg("outEdges_" + methodName, new TermList(edgeList));
        }

        private string OutEdgesLemmaName(int blockId)
        {
            return "outEdges_" + blockId;
        }

        private string NodeLemmaName(int blockId)
        {
            return "node_" + blockId;
        }

        private OuterDecl GetNodeToBlocksIsa(string methodName, CFGRepr cfg, IDictionary<Block, OuterDecl> blockToDecl)
        {
            var nodeList = new List<Term>();

            foreach (var b in cfg.GetBlocksBackwards())
                //left side of equation is block number expressed using constructors
                //right side of equation is command
                nodeList.Add(IsaCommonTerms.TermIdentFromName(blockToDecl[b].Name));

            return DefDecl.CreateWithoutArg("nodeToBlocks_" + methodName, new TermList(nodeList));
        }

        private DefDecl GetFunctionDeclarationsIsa(string methodName, IEnumerable<Function> functions)
        {
            //var equations = new List<Tuple<IList<Term>, Term>>();
            var fdecls = new List<Term>();


            foreach (var f in functions) fdecls.Add(IsaBoogieTerm.FunDecl(f, varTranslationFactory));

            return DefDecl.CreateWithoutArg(FunctionDeclarationsName(methodName), new TermList(fdecls));
        }

        private string FunctionDeclarationsName(string methodName)
        {
            return "fdecls_" + methodName;
        }

        private string PreconditionDeclarationName(string methodName)
        {
            return "pres";
        }

        private string PostconditionDeclarationName(string methodName)
        {
            return "post";
        }

        private DefDecl GetVariableDeclarationsIsa(string varKind, string methodName, IEnumerable<Variable> variables)
        {
            var typeIsaVisitor = new TypeIsaVisitor(varTranslation.TypeVarTranslation);

            var vdecls = new List<Term>();

            foreach (var v in variables)
                if (varTranslation.VarTranslation.TryTranslateVariableId(v, out var resId, out _))
                {
                    var vType = typeIsaVisitor.Translate(v.TypedIdent.Type);
                    vdecls.Add(new TermTuple(new List<Term> {resId, vType}));
                }
                else
                {
                    throw new ProofGenUnexpectedStateException(GetType(), "Cannot translate variable " + v.Name);
                }

            var equation = new Tuple<IList<Term>, Term>(new List<Term>(), new TermList(vdecls));
            return new DefDecl(VariableDeclarationsName(varKind, methodName), IsaBoogieType.VariableDeclsType,
                equation);
        }

        private string VariableDeclarationsName(string varKind, string methodName)
        {
            return varKind + "_vdecls_" + methodName;
        }

        private DefDecl GetExprListIsa(string declName, IEnumerable<Expr> exprs)
        {
            var result = new List<Term>();
            foreach (var expr in exprs) result.Add(cmdIsaVisitor.Translate(expr).First());

            return DefDecl.CreateWithoutArg(declName, new TermList(result));
        }

        private DefDecl GetMethodBodyCFGDecl(string methodName, Term methodBodyCFG)
        {
            return DefDecl.CreateWithoutArg(CfgName(methodName), methodBodyCFG);
        }

        private string CfgName(string methodName)
        {
            return "G_" + methodName;
        }
    }
}