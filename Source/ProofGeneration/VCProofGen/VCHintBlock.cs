using System.Collections.Generic;
using Isabelle.Ast;
using Microsoft.Boogie;
using ProofGeneration.Util;

namespace ProofGeneration.VCProofGen
{
    internal class VCHintBlock
    {
        private VCHint[] _hints;
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

        public void TransformHintsForTrivialVc()
        {
          if (cmds.Length != _hints.Length)
          {
            throw new ProofGenUnexpectedStateException("Not same number of hints as commands in the block.");
          }
          
          VCHint[] newHints = new VCHint[cmds.Length];
          for (int i = 0; i < cmds.Length; i++)
          {
            if (!(cmds[i] is AssumeCmd))
            {
              throw new ProofGenUnexpectedStateException("Trivial VC but there are assert statements");
            }

            if (_hints[i] is AssumeSimpleHint assumeSimpleHint && assumeSimpleHint.hintType == AssumeSimpleHint.AssumeSimpleType.ASSUME_FALSE)
            {
                //don't change the hint, since may still want to prove that the execution goes to magic
                newHints[i] = _hints[i];
            }
            else
            {
              newHints[i] = new AssumeSimpleHint(AssumeSimpleHint.AssumeSimpleType.ASSUME_TRUE);
            }
          }

          _hints = newHints;
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