using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface.VariableTranslation;
using ProofGeneration.Isa;
using ProofGeneration.Util;

namespace ProofGeneration.BoogieIsaInterface
{
    class MultiCmdIsaVisitor
    {

        private readonly BasicCmdIsaVisitor basicCmdVisitor;

        public MultiCmdIsaVisitor(BasicCmdIsaVisitor basicCmdVisitor)
        {
            this.basicCmdVisitor = basicCmdVisitor;
        }

        public MultiCmdIsaVisitor(IsaUniqueNamer uniqueNamer, IVariableTranslationFactory varTranslationFactory) : 
            this(new BasicCmdIsaVisitor(uniqueNamer, varTranslationFactory))
        {

        }

        public MultiCmdIsaVisitor(IVariableTranslationFactory varTranslationFactory) : this(new BasicCmdIsaVisitor(varTranslationFactory))
        { 
            
        }

        public IList<Term> Translate(Absy cmd)
        {            
            if(cmd is HavocCmd havocCmd)
            {
                return TranslateHavocCmd(havocCmd);
            } else            
            {
                return new List<Term>() { basicCmdVisitor.Translate(cmd) };
            }
        }

        public IList<Term> Translate(IList<Cmd> cmds)
        {
            List<Term> cmdsIsa = new List<Term>();

            foreach (Cmd cmd in cmds)
            {
                cmdsIsa.AddRange(Translate(cmd));
            }

            return cmdsIsa;
        }

        private Term TranslateIdentifierExpr(IdentifierExpr id)
        {
            return basicCmdVisitor.GetIdFromIdentifierExpr(id);
        }

        //desugar into single havoc commands
        private IList<Term> TranslateHavocCmd(HavocCmd node)
        {
            IEnumerable<Term> varResults = node.Vars.Select(var => TranslateIdentifierExpr(var));

            IList<Term> results = new List<Term>();

            foreach(Term v in varResults)
            {
                results.Add(IsaBoogieTerm.Havoc(v));
            }

            return results;
        }

    }
}
