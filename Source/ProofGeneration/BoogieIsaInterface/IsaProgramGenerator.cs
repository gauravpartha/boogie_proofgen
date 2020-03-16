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

        public Theory GetIsaProgram(Implementation impl, CFGRepr cfg, string thyName)
        {
            string methodName = impl.Proc.Name;            

            Term entry = new IntConst(Microsoft.Basetypes.BigNum.FromInt(cfg.GetUniqueIntLabel(cfg.entry)));

            OuterDecl outEdges = GetOutEdgesIsa(methodName, cfg);
            OuterDecl nodesToBlocks = GetNodeToBlocksIsa(methodName, cfg);

            Term nodes = GetNodeSet(cfg);

            Term parameters = GetVariableDeclarationsIsa(impl.InParams);
            Term localVariables = GetVariableDeclarationsIsa(impl.LocVars);

            Term methodBodyCFG = 
                IsaBoogieTerm.MethodCFGBody(
                    entry, nodes, IsaCommonTerms.TermIdentFromName(outEdges.name), IsaCommonTerms.TermIdentFromName(nodesToBlocks.name)
                );

            Term method = IsaBoogieTerm.Method(methodName, parameters, localVariables, methodBodyCFG);

            Term program = IsaBoogieTerm.Program(new List<Term>(), new List<Term>() { method });

            var list = new List<Tuple<IList<Term>, Term>>
            {
                new Tuple<IList<Term>, Term>(new List<Term>(), program)
            };

            OuterDecl programDefinition = new DefDecl("ProgramM", new Tuple<IList<Term>, Term>(new List<Term>(), program));

            IList<OuterDecl> outerDecls =
                new List<OuterDecl>()
                {
                    outEdges, nodesToBlocks, programDefinition
                };

            return new Theory(thyName, new List<string>() { "Lang" }, outerDecls);
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
            var cmdIsaVisitor = new MultiCmdIsaVisitor();

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

        private Term GetVariableDeclarationsIsa(IList<Variable> variables)
        {
            IList<Term> result = new List<Term>();

            var typeIsaVisitor = new TypeIsaVisitor();

            foreach (var v in variables)
            {
                Term vIsa = new StringConst(v.Name);
                Term tyIsa = typeIsaVisitor.Translate(v.TypedIdent.Type);

                result.Add(new TermTuple(new List<Term>() { vIsa, tyIsa }));
            }

            return new TermList(result);
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

