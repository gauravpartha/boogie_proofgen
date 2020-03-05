using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
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

        public MultiCmdIsaVisitor(IsaUniqueNamer uniqueNamer) : this(new BasicCmdIsaVisitor(uniqueNamer))
        {

        }

        public MultiCmdIsaVisitor() : this(new BasicCmdIsaVisitor())
        { 
            
        }

        public IList<Term> Translate(Absy cmd)
        {            
            if(cmd is AssignCmd assignCmd)
            {
                return TranslateAssignCmd(assignCmd);
            } else if(cmd is HavocCmd havocCmd)
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

        //desugar into single assignments
        private IList<Term> TranslateAssignCmd(AssignCmd node)
        {
            if ((node.Lhss.Count != node.Rhss.Count))
            {
                throw new ProofGenUnexpectedStateException(typeof(MultiCmdIsaVisitor), "different number of lhs and rhs");
            }

            IEnumerable<Term> lhsResults = node.Lhss.Select(lhs => basicCmdVisitor.Translate(lhs));
            IEnumerable<Term> rhsResults = node.Rhss.Select(rhs => basicCmdVisitor.Translate(rhs));

            IList<Term> results = new List<Term>();
            lhsResults.ZipDo(rhsResults, (lhs, rhs) => results.Add(IsaBoogieTerm.Assign(lhs, rhs)));

            return results;
        }

        //desugar into single havoc commands
        private IList<Term> TranslateHavocCmd(HavocCmd node)
        {
            IEnumerable<Term> varResults = node.Vars.Select(var => new StringConst(basicCmdVisitor.GetStringFromIdentifierExpr(var)));

            IList<Term> results = new List<Term>();

            foreach(Term v in varResults)
            {
                results.Add(IsaBoogieTerm.Havoc(v));
            }

            return results;
        }

    }
}
