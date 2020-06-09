using Microsoft.Boogie;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace ProofGeneration.VCProofGen
{
    class VCHintBlock
    {
        private readonly Cmd[] cmds;
        public VCHint[] Hints { get; private set; }

        //when this conjunct will become active, then if ImplAtTopLevel is true,
        //then the nestLevel assumes that the original implication with which the
        //the nestLevel was originally computed is still 
        private ISet<VCHint> HintAwareOfUpdate = new HashSet<VCHint>();
             

        private int nextCmd;

        public VCHintBlock(Block block)
        {
            cmds = block.cmds.ToArray();
            nextCmd = cmds.Length - 1;
            Hints = new VCHint[cmds.Length];
        }

        public void AddHint(Cmd cmd, VCHint hint)
        {
            if (nextCmd < 0 || cmd != cmds[nextCmd])
            {
                throw new ProofGenUnexpectedStateException(this.GetType(), "current hint database does not match cmd");
            }

            Hints[nextCmd] = hint;

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
