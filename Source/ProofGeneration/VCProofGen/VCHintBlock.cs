using System.Collections.Generic;
using Isabelle.Ast;
using Microsoft.Boogie;
using ProofGeneration.Util;

namespace ProofGeneration.VCProofGen
{
    internal class VCHintBlock
    {
        private readonly VCHint[] _hints;
        private readonly Cmd[] cmds;

        private int nextCmd;

        public VCHintBlock(Block block)
        {
            cmds = block.cmds.ToArray();
            nextCmd = cmds.Length - 1;
            _hints = new VCHint[cmds.Length];
            OuterDecls = new List<OuterDecl>();
        }

        //declarations required for proof
        public IList<OuterDecl> OuterDecls { get; }

        public IEnumerable<VCHint> Hints()
        {
            var result = new List<VCHint>();
            //ignore hints after a hint that solves the complete goal
            foreach (var hint in _hints)
            {
                result.Add(hint);

                if (hint.IsFinal())
                {
                    break;
                }
            }

            return result;
        }

        public void AddHint(Cmd cmd, VCHint hint)
        {
            if (nextCmd < 0 || cmd != cmds[nextCmd])
            {
                throw new ProofGenUnexpectedStateException(GetType(), "current hint database does not match cmd");
            }

            _hints[nextCmd] = hint;

            nextCmd--;
        }

        public void AddRequiredDecls(List<LemmaDecl> decls)
        {
            OuterDecls.AddRange(decls);
        }

        public void AddRequiredDecl(OuterDecl decl)
        {
            OuterDecls.Add(decl);
        }

        private int NumOfCommands(VCHint hint)
        {
            if (hint is AssumeConjHint assumeConjHint)
            {
                return assumeConjHint.NumCommands;
            }

            throw new ProofGenUnexpectedStateException(GetType(), "unexpected hint");
        }
    }
}