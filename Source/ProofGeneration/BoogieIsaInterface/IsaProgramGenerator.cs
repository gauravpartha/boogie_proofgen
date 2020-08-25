using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Text;
using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.CFGRepresentation;
using ProofGeneration.Isa;
using ProofGeneration.Util;

namespace ProofGeneration
{
    class IsaProgramGenerator
    {
        private readonly MultiCmdIsaVisitor cmdIsaVisitor = new MultiCmdIsaVisitor();
        private readonly TypeIsaVisitor typeIsaVisitor = new TypeIsaVisitor();

        public IsaProgramRepr GetIsaProgram(
            string localeName,
            string procName,
            BoogieMethodData methodData,
            CFGRepr cfg,
            out IList<OuterDecl> decls
            )
        {
            Term entry = new IntConst(Microsoft.Basetypes.BigNum.FromInt(cfg.GetUniqueIntLabel(cfg.entry)));

            OuterDecl outEdges = GetOutEdgesIsa(procName, cfg);
            OuterDecl nodesToBlocks = GetNodeToBlocksIsa(procName, cfg);

            Term nodes = GetNodeSet(cfg);

            DefDecl funcs = GetFunctionDeclarationsIsa(procName, methodData.Functions);
            DefDecl axiomsDecl = GetAxioms(procName, methodData.Axioms);

            OuterDecl parameters = GetVariableDeclarationsIsa("inParams", procName, methodData.InParams);
            OuterDecl localVariables = GetVariableDeclarationsIsa("localVars", procName, methodData.Locals);

            Term methodBodyCFG =
                IsaBoogieTerm.MethodCFGBody(
                    entry, nodes, IsaCommonTerms.TermIdentFromName(outEdges.name), IsaCommonTerms.TermIdentFromName(nodesToBlocks.name)
                );

            DefDecl methodBodyDecl = GetMethodBodyCFGDecl(procName, methodBodyCFG);

            Term method = IsaBoogieTerm.Method(procName, IsaCommonTerms.TermIdentFromName(parameters.name), IsaCommonTerms.TermIdentFromName(localVariables.name), IsaCommonTerms.TermIdentFromName(methodBodyDecl.name));

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

            decls =
                new List<OuterDecl>()
                {
                    outEdges, nodesToBlocks, funcs, axiomsDecl, parameters, localVariables, methodBodyDecl, programDefinition
                };

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
                if(axTerms.Count != 1) { throw new ProofGenUnexpectedStateException(GetType(), "axiom not translated into single term"); };
                axiomsExpr.Add(axTerms.First());
            }
            var equation = new Tuple<IList<Term>, Term>(new List<Term>(), new TermList(axiomsExpr));

            return new DefDecl("axioms_" + methodName, equation);
        }

        private OuterDecl GetOutEdgesIsa(string methodName, CFGRepr cfg)
        {
            var equations = new List<Tuple<IList<Term>, Term>>();

            foreach(Block b in cfg.GetBlocksForwards())
            {
                //left side of equation is block number expressed using constructors
                //right side of equation is set repr

                Term lhs = new NatConst(cfg.GetUniqueIntLabel(b));

                IEnumerable<Block> outgoing = cfg.GetSuccessorBlocks(b);

                Term rhs = new TermSet(outgoing.Select(b_succ => new NatConst(cfg.GetUniqueIntLabel(b_succ))));

                BasicUtil.AddEquation(lhs, rhs, equations);
            }

            //empty set for remaining cases
            BasicUtil.AddEquation(new TermIdent(new Wildcard()), new TermSet(new List<Term>()), equations);

            return new FunDecl("outEdges_"+methodName, new ArrowType(IsaBoogieType.GetCFGNodeType(), IsaCommonTypes.GetSetType(IsaBoogieType.GetCFGNodeType())), equations);
        }

        private OuterDecl GetNodeToBlocksIsa(string methodName, CFGRepr cfg)
        {
            var equations = new List<Tuple<IList<Term>, Term>>();

            foreach (Block b in cfg.GetBlocksForwards())
            {

                //left side of equation is block number expressed using constructors
                //right side of equation is command
                Term lhs = new NatConst(cfg.GetUniqueIntLabel(b));

                IList<Term> cmdsIsa = cmdIsaVisitor.Translate(b.Cmds);

                Term rhs = IsaCommonTerms.SomeOption(new TermList(cmdsIsa));

                BasicUtil.AddEquation(lhs, rhs, equations);
            }

            //None for remaining cases
            BasicUtil.AddEquation(new TermIdent(new Wildcard()), IsaCommonTerms.NoneOption(), equations);

            return new FunDecl("nodeToBlocks_"+methodName, new ArrowType(IsaBoogieType.GetCFGNodeType(), IsaCommonTypes.GetOptionType(IsaBoogieType.GetBlockType())), equations);
        }

        private DefDecl GetFunctionDeclarationsIsa(string methodName, IEnumerable<Function> functions)
        {
            var typeIsaVisitor = new TypeIsaVisitor();
            //var equations = new List<Tuple<IList<Term>, Term>>();
            var fdecls = new List<Term>();


            foreach (var f in functions)
            {
                fdecls.Add(IsaBoogieTerm.FunDecl(f));
            }

            var  equation = new Tuple<IList<Term>, Term>(new List<Term>(), new TermList(fdecls));

            return new DefDecl("fdecls" + "_" + methodName, equation);
        }

        private DefDecl GetVariableDeclarationsIsa(string varKind, string methodName, IEnumerable<Variable> variables)
        {
            var typeIsaVisitor = new TypeIsaVisitor();

            var vdecls = new List<Term>();

            foreach (var v in variables)
            {
                Term vName = new StringConst(v.Name);
                Term vType = typeIsaVisitor.Translate(v.TypedIdent.Type);

                vdecls.Add(new TermTuple(new List<Term> { vName, vType }));               
            }

            var equation = new Tuple<IList<Term>, Term>(new List<Term>(), new TermList(vdecls));
            return new DefDecl(varKind + "_vdecls_" + methodName, equation);
        }

        private DefDecl GetMethodBodyCFGDecl(string methodName, Term methodBodyCFG)
        {
            var equation = new Tuple<IList<Term>, Term>(new List<Term>(), methodBodyCFG);
            return new DefDecl("G_" + methodName, equation);
        }

        private Term GetNodeSet(CFGRepr cfg)
        {
            var labels = cfg.GetBlocksForwards().Select(b => cfg.GetUniqueIntLabel(b));
            var labelTerms = labels.Select(i => new NatConst(i));

            return new TermSet(labelTerms);
        }

        private string NodeToBlockName(string methodName)
        {
            return "nodeToBlock_" + methodName;
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

