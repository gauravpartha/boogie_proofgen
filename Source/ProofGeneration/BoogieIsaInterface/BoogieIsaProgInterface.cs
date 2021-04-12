using System.Collections.Generic;
using Microsoft.Boogie;

namespace ProofGeneration.BoogieIsaInterface
{
    public class BoogieIsaProgInterface
    {
        public IDictionary<string, IProgramAccessor> ProgramAccessors { get; }
        public IGlobalProgramAccessor GlobalDataAccessor { get; }

        public BoogieIsaProgInterface(IDictionary<string, IProgramAccessor> programAccessors,
            IGlobalProgramAccessor globalDataAccessor)
        {
            ProgramAccessors = programAccessors;
            GlobalDataAccessor = globalDataAccessor;
        }
    }
}