using Microsoft.Boogie;
using System.Collections.Generic;

namespace ProofGeneration.VCProofGen
{
    class VCHintBlock
    {
        private readonly Cmd[] cmds;
        private readonly VCHint[] _hints;

        public IEnumerable<VCHint> Hints()
        {
            List<VCHint> result = new List<VCHint>();
            //ignore hints after a hint that solves the complete goal
            foreach (VCHint hint in _hints)
            {
                result.Add(hint);

                if (hint.IsFinal())
                {
                    break;
                }
            }

            return result;
        }             

        private int nextCmd;

        public VCHintBlock(Block block)
        {
            cmds = block.cmds.ToArray();
            nextCmd = cmds.Length - 1;
            _hints = new VCHint[cmds.Length];
        }

        public void AddHint(Cmd cmd, VCHint hint)
        {
            if (nextCmd < 0 || cmd != cmds[nextCmd])
            {
                throw new ProofGenUnexpectedStateException(this.GetType(), "current hint database does not match cmd");
            }

            _hints[nextCmd] = hint;

            nextCmd--;
        }

        private int NumOfCommands(VCHint hint)
        {
            if(hint is AssumeConjHint assumeConjHint)
            {
                return assumeConjHint.NumCommands;
            } else
            {
                throw new ProofGenUnexpectedStateException(GetType(), "unexpected hint");
            }
        }

    }
}
