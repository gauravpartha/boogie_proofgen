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
        MultiCmdIsaVisitor cmdIsaVisitor = new MultiCmdIsaVisitor();

        public LocaleDecl GetIsaProgram(
            string localeName, 
            string procName,
            IEnumerable<Function> functions,
            IEnumerable<Variable> inParams, 
            IEnumerable<Variable> localVars, 
            IEnumerable<Variable> outParams, 
            CFGRepr cfg)
        {
            Term entry = new IntConst(Microsoft.Basetypes.BigNum.FromInt(cfg.GetUniqueIntLabel(cfg.entry)));

            OuterDecl outEdges = GetOutEdgesIsa(procName, cfg);
            OuterDecl nodesToBlocks = GetNodeToBlocksIsa(procName, cfg);

            Term nodes = GetNodeSet(cfg);

            OuterDecl funcs = GetFunctionDeclarationsIsa(procName, functions);
            OuterDecl parameters = GetVariableDeclarationsIsa("inParams", procName, inParams);
            OuterDecl localVariables = GetVariableDeclarationsIsa("localVars", procName, localVars);

            Term methodBodyCFG = 
                IsaBoogieTerm.MethodCFGBody(
                    entry, nodes, IsaCommonTerms.TermIdentFromName(outEdges.name), IsaCommonTerms.TermIdentFromName(nodesToBlocks.name)
                );

            Term method = IsaBoogieTerm.Method(procName, IsaCommonTerms.TermIdentFromName(parameters.name), IsaCommonTerms.TermIdentFromName(localVariables.name), methodBodyCFG);

            Term program = IsaBoogieTerm.Program(IsaCommonTerms.TermIdentFromName(funcs.name), new List<Term>() { method });

            var list = new List<Tuple<IList<Term>, Term>>
            {
                new Tuple<IList<Term>, Term>(new List<Term>(), program)
            };

            OuterDecl programDefinition = new DefDecl("ProgramM", new Tuple<IList<Term>, Term>(new List<Term>(), program));

            IList<OuterDecl> outerDecls =
                new List<OuterDecl>()
                {
                    outEdges, nodesToBlocks, funcs, parameters, localVariables, programDefinition
                };

            return new LocaleDecl(localeName, ContextElem.CreateEmptyContext(), outerDecls);
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

            return new FunDecl("nodeToBlocks_"+methodName, new ArrowType(IsaBoogieType.GetCFGNodeType(), IsaBoogieType.GetBlockType()), equations);
        }

        private OuterDecl GetFunctionDeclarationsIsa(string methodName, IEnumerable<Function> functions)
        {
            var typeIsaVisitor = new TypeIsaVisitor();
            var equations = new List<Tuple<IList<Term>, Term>>();

            /* TODO

            foreach(var f in functions)
            {
                Term lhs = new StringConst(f.Name);
                Term rhs = IsaCommonTerms.SomeOption(typeIsaVisitor.Translate(f.))
            }

            */
            BasicUtil.AddEquation(new TermIdent(new Wildcard()), IsaCommonTerms.NoneOption(), equations);

            return new FunDecl("funDecl" + "_" + methodName, new ArrowType(IsaBoogieType.FnameType(), IsaCommonTypes.GetOptionType(IsaBoogieType.BoogieType())), equations);
        }

        private OuterDecl GetVariableDeclarationsIsa(string varKind, string methodName, IEnumerable<Variable> variables)
        {
            var typeIsaVisitor = new TypeIsaVisitor();

            var equations = new List<Tuple<IList<Term>, Term>>();

            foreach (var v in variables)
            {
                Term lhs = new StringConst(v.Name);
                Term rhs = IsaCommonTerms.SomeOption(typeIsaVisitor.Translate(v.TypedIdent.Type));

                
                BasicUtil.AddEquation(lhs, rhs, equations);
            }

            //None for remaining cases
            BasicUtil.AddEquation(new TermIdent(new Wildcard()), IsaCommonTerms.NoneOption(), equations);

            return new FunDecl(varKind + "_" + methodName, new ArrowType(IsaBoogieType.VnameType(), IsaCommonTypes.GetOptionType(IsaBoogieType.BoogieType())), equations);
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

