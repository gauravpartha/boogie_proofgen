using System;
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

        public IsaProgramRepr GetIsaProgram(
            string localeName,
            string procName,
            BoogieMethodData methodData,
            IVariableTranslationFactory varTranslationFactory,
            CFGRepr cfg,
            out IList<OuterDecl> decls,
            out IDictionary<Block, OuterDecl> blockToDecl
            )
        {
            this.varTranslationFactory = varTranslationFactory;
            cmdIsaVisitor = new MultiCmdIsaVisitor(varTranslationFactory);
            Term entry = new IntConst(Microsoft.BaseTypes.BigNum.FromInt(cfg.GetUniqueIntLabel(cfg.entry)));

            OuterDecl outEdges = GetOutEdgesIsa(procName, cfg);
            
            blockToDecl = BlockToDecl(cfg);
            OuterDecl nodesToBlocks = GetNodeToBlocksIsa(procName, cfg, blockToDecl);

            DefDecl funcs = GetFunctionDeclarationsIsa(procName, methodData.Functions);
            DefDecl axiomsDecl = GetAxioms(procName, methodData.Axioms);

            OuterDecl parameters = GetVariableDeclarationsIsa("inParams", procName, methodData.InParams);
            OuterDecl localVariables = GetVariableDeclarationsIsa("localVars", procName, methodData.Locals);

            Term methodBodyCFG =
                IsaBoogieTerm.MethodCFGBody(
                    entry, IsaCommonTerms.TermIdentFromName(outEdges.name), IsaCommonTerms.TermIdentFromName(nodesToBlocks.name)
                );

            DefDecl methodBodyDecl = GetMethodBodyCFGDecl(procName, methodBodyCFG);

            Term method = IsaBoogieTerm.Method(procName, methodData.TypeParams.Count(), IsaCommonTerms.TermIdentFromName(parameters.name), IsaCommonTerms.TermIdentFromName(localVariables.name), IsaCommonTerms.TermIdentFromName(methodBodyDecl.name));

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
             
            decls = new List<OuterDecl>(blockToDecl.Values);
            decls.AddRange(
                new List<OuterDecl>()
                {
                    outEdges, nodesToBlocks, funcs, axiomsDecl, parameters, localVariables, methodBodyDecl, programDefinition
                });

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

        private Dictionary<Block, OuterDecl> BlockToDecl(CFGRepr cfg)
        {
            var dict = new Dictionary<Block, OuterDecl>();
            foreach (Block b in cfg.GetBlocksForwards())
            {
                //left side of equation is block number expressed using constructors
                //right side of equation is command
                var translatedBlocks = cmdIsaVisitor.Translate(b.Cmds);
                DefDecl blockDecl = new DefDecl("block_" + cfg.GetUniqueIntLabel(b),
                    Tuple.Create((IList<Term>)new List<Term>(), (Term) new TermList(translatedBlocks))
                );
                dict.Add(b, blockDecl);
            }

            return dict;
        }

        private OuterDecl GetOutEdgesIsa(string methodName, CFGRepr cfg)
        {
            //var equations = new List<Tuple<IList<Term>, Term>>();
            var edgeList = new List<Term>();

            foreach(Block b in cfg.GetBlocksForwards())
            {
                IEnumerable<Block> outgoing = cfg.GetSuccessorBlocks(b);
                Term edges = new TermList(outgoing.Select(b_succ => (Term) new NatConst(cfg.GetUniqueIntLabel(b_succ))).ToList());
                edgeList.Add(edges);
            }

            //empty set for remaining cases
            return new DefDecl("outEdges_" + methodName,
                new Tuple<IList<Term>, Term>(new List<Term>(), new TermList(edgeList)));
        }

        private OuterDecl GetNodeToBlocksIsa(string methodName, CFGRepr cfg, IDictionary<Block, OuterDecl> blockToDecl)
        {
            var nodeList = new List<Term>();

            foreach (Block b in cfg.GetBlocksForwards())
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
            var typeIsaVisitor = new TypeIsaVisitor(varTranslationFactory.CreateTranslation().TypeVarTranslation);

            var vdecls = new List<Term>();

            foreach (var v in variables)
            {
                Term vName = new StringConst(v.Name);
                Term vType = typeIsaVisitor.Translate(v.TypedIdent.Type);

                vdecls.Add( vType ); 
            }

            var equation = new Tuple<IList<Term>, Term>(new List<Term>(), new TermList(vdecls));
            return new DefDecl(varKind + "_vdecls_" + methodName, equation);
        }

        private DefDecl GetMethodBodyCFGDecl(string methodName, Term methodBodyCFG)
        {
            var equation = new Tuple<IList<Term>, Term>(new List<Term>(), methodBodyCFG);
            return new DefDecl("G_" + methodName, equation);
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

