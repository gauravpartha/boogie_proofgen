using System;
using System.Collections;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.BoogieIsaInterface.VariableTranslation;
using ProofGeneration.CFGRepresentation;
using ProofGeneration.Isa;
using ProofGeneration.Util;

namespace ProofGeneration
{
    class IsaProgramGenerator
    {
        private MultiCmdIsaVisitor cmdIsaVisitor;
        private IVariableTranslationFactory varTranslationFactory;
        private BoogieVariableTranslation varTranslation;

        public IsaProgramRepr GetIsaProgram(
            string theoryName,
            string procName,
            BoogieMethodData methodData,
            IVariableTranslationFactory varTranslationFactory,
            CFGRepr cfg,
            out IList<OuterDecl> decls,
            out IsaBlockInfo blockInfo
            )
        {
            this.varTranslationFactory = varTranslationFactory;
            varTranslation = varTranslationFactory.CreateTranslation();
            cmdIsaVisitor = new MultiCmdIsaVisitor(varTranslationFactory);
            Term entry = new IntConst(Microsoft.BaseTypes.BigNum.FromInt(cfg.GetUniqueIntLabel(cfg.entry)));

            OuterDecl outEdges = GetOutEdgesIsa(procName, cfg, out Dictionary<Block, LemmaDecl> edgeLemmas);
            blockInfo = BlockToInfo(theoryName, procName, cfg, edgeLemmas);
            OuterDecl nodesToBlocks = GetNodeToBlocksIsa(procName, cfg, blockInfo.BlockCmdsDefs);

            DefDecl funcs = GetFunctionDeclarationsIsa(procName, methodData.Functions);
            DefDecl axiomsDecl = GetAxioms(procName, methodData.Axioms);

            OuterDecl parameters = GetVariableDeclarationsIsa("inParams", procName, methodData.InParams);
            OuterDecl localVariables = GetVariableDeclarationsIsa("localVars", procName, methodData.Locals);

            TermList modifiedVariables = new TermList(new List<Term>()); //TODO
            OuterDecl preconditions = GetPreconditionsIsa(procName, methodData.Preconditions);
            OuterDecl postconditions = GetPostconditionsIsa(procName, methodData.Postcondtions);

            Term methodBodyCFG =
                IsaBoogieTerm.MethodCFGBody(
                    entry, IsaCommonTerms.TermIdentFromName(outEdges.name), IsaCommonTerms.TermIdentFromName(nodesToBlocks.name)
                );

            DefDecl methodBodyDecl = GetMethodBodyCFGDecl(procName, methodBodyCFG);

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

            //TODO: global variables
            Term program = IsaBoogieTerm.Program(IsaCommonTerms.TermIdentFromName(funcs.name),
                new TermList(new List<Term>()),
                new TermList(new List<Term>()),
                IsaCommonTerms.TermIdentFromName(axiomsDecl.name),
                new List<Term>() { method });

            var list = new List<Tuple<IList<Term>, Term>>
            {
                new Tuple<IList<Term>, Term>(new List<Term>(), program)
            };

            OuterDecl programDefinition = new DefDecl("ProgramM", new Tuple<IList<Term>, Term>(new List<Term>(), program));
             
            decls = new List<OuterDecl>();
            decls.AddRange(blockInfo.BlockCmdsDefs.Values);
            decls.AddRange(
        new List<OuterDecl>()
                {
                    outEdges, nodesToBlocks, funcs, axiomsDecl, parameters, localVariables, preconditions, postconditions, methodBodyDecl, programDefinition
                });
            decls.AddRange(blockInfo.BlockCmdsLemmas.Values);
            decls.AddRange(blockInfo.BlockOutEdgesLemmas.Values);
            
            return new IsaProgramRepr(
                IsaCommonTerms.TermIdentFromDecl(funcs), 
                IsaCommonTerms.TermIdentFromDecl(axiomsDecl), 
                IsaCommonTerms.TermIdentFromDecl(parameters),
                IsaCommonTerms.TermIdentFromDecl(localVariables),
                IsaCommonTerms.TermIdentFromDecl(methodBodyDecl));
        }

        private DefDecl GetAxioms(string methodName, IEnumerable<Axiom> axioms)
        {
            var axiomsExpr = new List<Term>();
            foreach (Axiom ax in axioms)
            {
                IList<Term> axTerms = cmdIsaVisitor.Translate(ax.Expr);
                if(axTerms.Count != 1) { throw new ProofGenUnexpectedStateException(GetType(), "axiom not translated into single term"); }
                axiomsExpr.Add(axTerms.First());
            }
            var equation = new Tuple<IList<Term>, Term>(new List<Term>(), new TermList(axiomsExpr));

            return new DefDecl("axioms_" + methodName, equation);
        }

        private IsaBlockInfo BlockToInfo(string theoryName, string methodName, CFGRepr cfg, Dictionary<Block, LemmaDecl> edgeLemmas)
        {
            //TODO: redundant to have extra indexing map, re-use labelling map
            var blockToCounter = new Dictionary<Block, int>();
            var blockToDecl = new Dictionary<Block, OuterDecl>();
            var blockToNodesLemmas = new Dictionary<Block, LemmaDecl>(); 

            var cfgTerm = IsaCommonTerms.TermIdentFromName(CfgName(methodName));
            var cfgDef = CfgName(methodName) + "_def";
            var nodeToBlockDef = "nodeToBlocks_" + methodName + "_def";

            foreach (Block b in cfg.GetBlocksBackwards())
            {
                //left side of equation is block number expressed using constructors
                //right side of equation is command
                var translatedBlocks = cmdIsaVisitor.Translate(b.Cmds);
                DefDecl blockDecl = new DefDecl("block_" + cfg.GetUniqueIntLabel(b),
                    Tuple.Create((IList<Term>)new List<Term>(), (Term) new TermList(translatedBlocks))
                );
                blockToDecl.Add(b, blockDecl);
                
                int blockLabel = cfg.GetUniqueIntLabel(b);
                
                // nodes lemma
                {
                    LemmaDecl nodeDecl = new LemmaDecl(
                        NodeLemmaName(blockLabel),
                        ContextElem.CreateEmptyContext(),
                        TermBinary.Eq( IsaBoogieTerm.NodeToBlock(cfgTerm, blockLabel), 
                            IsaCommonTerms.TermIdentFromName(blockDecl.name)),
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
            
            foreach(Block b in cfg.GetBlocksBackwards())
            {
                IEnumerable<Block> outgoing = cfg.GetSuccessorBlocks(b);
                Term edges = new TermList(outgoing.Select(b_succ => (Term) new NatConst(cfg.GetUniqueIntLabel(b_succ))).ToList());
                edgeList.Add(edges);
                // edges lemma
                
                int blockLabel = cfg.GetUniqueIntLabel(b);
                LemmaDecl edgeDecl = new LemmaDecl(OutEdgesLemmaName(blockLabel),
                    ContextElem.CreateEmptyContext(),
                    TermBinary.Eq(IsaBoogieTerm.OutEdges(cfgTerm, blockLabel), edges),
                    new Proof(new List<string> {"by " + ProofUtil.Simp(cfgDef, outEdgesDef)}));

                edgeLemmas.Add(b, edgeDecl);
            }

            //empty set for remaining cases
            return new DefDecl("outEdges_" + methodName,
                new Tuple<IList<Term>, Term>(new List<Term>(), new TermList(edgeList)));
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

            foreach (Block b in cfg.GetBlocksBackwards())
            {
                //left side of equation is block number expressed using constructors
                //right side of equation is command
                nodeList.Add(IsaCommonTerms.TermIdentFromName(blockToDecl[b].name));
            }

            return new DefDecl("nodeToBlocks_"+methodName, new Tuple<IList<Term>, Term>(new List<Term>(), 
                new TermList(nodeList)) );
        }

        private DefDecl GetFunctionDeclarationsIsa(string methodName, IEnumerable<Function> functions)
        {
            //var equations = new List<Tuple<IList<Term>, Term>>();
            var fdecls = new List<Term>();


            foreach (var f in functions)
            {
                fdecls.Add(IsaBoogieTerm.FunDecl(f, varTranslationFactory));
            }

            var  equation = new Tuple<IList<Term>, Term>(new List<Term>(), new TermList(fdecls));

            return new DefDecl("fdecls" + "_" + methodName, equation);
        }

        private DefDecl GetVariableDeclarationsIsa(string varKind, string methodName, IEnumerable<Variable> variables)
        {
            var typeIsaVisitor = new TypeIsaVisitor(varTranslation.TypeVarTranslation);

            var vdecls = new List<Term>();

            foreach (var v in variables)
            {
                if (varTranslation.VarTranslation.TryTranslateVariableId(v, out Term resId, out bool isBoundVar))
                {
                    Term vType = typeIsaVisitor.Translate(v.TypedIdent.Type);
                    vdecls.Add(new TermTuple(new List<Term> {resId, vType}));
                }
                else
                {
                    throw new ProofGenUnexpectedStateException(GetType(),"Cannot translate variable " + v.Name);
                }
            }

            var equation = new Tuple<IList<Term>, Term>(new List<Term>(), new TermList(vdecls));
            return new DefDecl(varKind + "_vdecls_" + methodName, IsaBoogieType.VariableDeclsType, equation);
        }

        private DefDecl GetPreconditionsIsa(string methodName, IEnumerable<Requires> pres)
        {
            return GetExprListIsa("pre_"+methodName, new Func<Requires,Expr>(r => r.Condition), pres);
        }

        private DefDecl GetPostconditionsIsa(string methodName, IEnumerable<Ensures> post)
        {
            return GetExprListIsa("post_"+methodName, new Func<Ensures,Expr>(r => r.Condition), post);
        }

        private DefDecl GetExprListIsa<T>(string declName, Func<T, Expr> elemToExpr, IEnumerable<T> elems)
        {
            var result = new List<Term>();
            foreach (var elem in elems)
            {
               result.Add(cmdIsaVisitor.Translate(elemToExpr(elem)).First()); 
            }
            return new DefDecl(declName, new Tuple<IList<Term>, Term>(new List<Term>(), new TermList(result)));
        }
        
        private DefDecl GetMethodBodyCFGDecl(string methodName, Term methodBodyCFG)
        {
            var equation = new Tuple<IList<Term>, Term>(new List<Term>(), methodBodyCFG);
            return new DefDecl(CfgName(methodName), equation);
        }
        private string CfgName(string methodName) {
            return "G_" + methodName;
        }
    }
    

    public class IsaCFGGeneratorException : Exception
    {
        public enum Reason { VISITOR_NOT_FRESH, CFG_NOT_UNIQUE_ENTRY, CFG_NO_ENTRY}

        private readonly Reason _reason;

        public IsaCFGGeneratorException(Reason reason)
        {
            _reason = reason;
        }

    }
    
}

