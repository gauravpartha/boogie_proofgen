using System.Collections.Generic;
using System.Linq;
using Isabelle.Ast;
using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface.VariableTranslation;

namespace ProofGeneration.BoogieIsaInterface
{
    internal class MultiCmdIsaVisitor
    {
        private readonly BasicCmdIsaVisitor basicCmdVisitor;

        public MultiCmdIsaVisitor(BasicCmdIsaVisitor basicCmdVisitor)
        {
            this.basicCmdVisitor = basicCmdVisitor;
        }

        public MultiCmdIsaVisitor(IVariableTranslationFactory varTranslationFactory) : this(
            new BasicCmdIsaVisitor(varTranslationFactory))
        {
        }

        public IList<Term> Translate(Absy cmd)
        {
            if (cmd is HavocCmd havocCmd)
                return TranslateHavocCmd(havocCmd);
            return new List<Term> {basicCmdVisitor.Translate(cmd)};
        }

        public IList<Term> Translate(IList<Cmd> cmds)
        {
            var cmdsIsa = new List<Term>();

            foreach (var cmd in cmds) cmdsIsa.AddRange(Translate(cmd));

            return cmdsIsa;
        }

        private Term TranslateIdentifierExpr(IdentifierExpr id)
        {
            return basicCmdVisitor.GetIdFromIdentifierExpr(id);
        }

        //desugar into single havoc commands
        private IList<Term> TranslateHavocCmd(HavocCmd node)
        {
            var varResults = node.Vars.Select(var => TranslateIdentifierExpr(var));

            IList<Term> results = new List<Term>();

            foreach (var v in varResults) results.Add(IsaBoogieTerm.Havoc(v));

            return results;
        }
    }
}