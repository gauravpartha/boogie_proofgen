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

            if(hint is AssumeConjHint assumeConjHint && assumeConjHint.NestLevel >= 1)
            {
                /* potentially need to update subsequent commands, since
                 * A => B => C => D, may have been changed to ((A /\ B) /\ C) => D, where B C corresponds to 
                 * assume statements (or conjunctions of assume statements that have already been processed) 
                 * while the current command corresponds to A
                 * */

                void CheckAssume(Cmd c)
                {
                    if (!(c is AssumeCmd))
                    {
                        throw new ProofGenUnexpectedStateException(GetType(), "nest level incorporates commands that are not assumptions");
                    }
                }


                /* if A => B => C => D is turned into (A /\ (B /\ C)) => D (i.e., nestLevel = 2), we need to potentially update
                 * the hint of B. C does not have to be updated, because once A and B have been reduced, the remaining VC is C => D
                 * */
                {
                    int numCommandsInConjunct = 1;

                    int curConjunctId = nextCmd +  1;

                    if (curConjunctId >= cmds.Length || !(cmds[curConjunctId] is AssumeCmd))
                    {
                        throw new ProofGenUnexpectedStateException(GetType(), "nest level invalid");
                    }

                    for (int visitedConjuncts = 0;  visitedConjuncts < assumeConjHint.NumConjunctions - 1; visitedConjuncts++)
                    {
                        int nextConjunctId;

                        if (Hints[curConjunctId] is AssumeConjHint conjunctAssumeConjHint)
                        {
                            /* current conjunct consists of multiple assume statements
                                * We need to update two things:
                                * 1) the nest level of the first assume statement in this conjunct must be updated,
                                *    since we added a conjunction to the right of it
                                * 2) the nest level of all other assume statements in this conjunct must be increased by one,
                                *    so that the nest level is aware of the implication being turned to an conjunction
                                *    If the nest level is already aware of its corresponding implication being turned to a conjunction,
                                *    then nothing needs to be done.
                                * */
                            nextConjunctId = curConjunctId + conjunctAssumeConjHint.NumCommands;
                            if (nextConjunctId >= cmds.Length)
                                throw new ProofGenUnexpectedStateException(GetType(), "nest length incorrect");

                            if (!(Hints[nextConjunctId - 1] is AssumeConjHint finalAssumeInConjunct) || finalAssumeInConjunct.NestLevel != 0)
                            {
                                throw new ProofGenUnexpectedStateException(GetType(),
                                    "final command in conjunct does not have implies hint");
                            }

                            for (int i = curConjunctId + 1; i < nextConjunctId; i++)
                            {
                                if (Hints[i] is AssumeConjHint conjToBeUpdated)
                                {
                                    //sanity check: only the final command in the conjunct should nestLevel 0
                                    if ((i + 1 == nextConjunctId && conjToBeUpdated.NestLevel == 0) || (i + 1 != nextConjunctId && conjToBeUpdated.NestLevel > 0))
                                    {
                                        if (!HintAwareOfUpdate.Contains(conjToBeUpdated))
                                        {
                                            conjToBeUpdated.NestLevel++;
                                            HintAwareOfUpdate.Add(conjToBeUpdated);
                                        }
                                    }
                                    else
                                    {
                                        throw new ProofGenUnexpectedStateException(GetType(), "unexpected hint structure");
                                    }
                                }
                                else
                                {
                                    throw new ProofGenUnexpectedStateException(GetType(), "unexpected hint");
                                }
                            }

                            conjunctAssumeConjHint.NestLevel += 1; //update nestLevel of first assume in conjunct
                            HintAwareOfUpdate.Add(conjunctAssumeConjHint);
                            numCommandsInConjunct += conjunctAssumeConjHint.NumCommands;
                        } else
                        {
                            throw new ProofGenUnexpectedStateException(GetType(), "unexpected hint");
                        }

                        //check whether all commands that are part of the new left hand side are assume statements 
                        // (we already checked curConjunctId)
                        Enumerable.Range(curConjunctId + 1, nextConjunctId - curConjunctId).ToList().ForEach(i => CheckAssume(cmds[i]));
                        curConjunctId = nextConjunctId;
                    }

                    //also take into account final conjunct
                    assumeConjHint.NumCommands = numCommandsInConjunct + NumOfCommands(Hints[curConjunctId]);
                }

            } else if(hint is AssumeConjHint assumeConjHintOne && assumeConjHintOne.NestLevel == 0)
            {
                assumeConjHintOne.NumCommands = 1;
            }

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
