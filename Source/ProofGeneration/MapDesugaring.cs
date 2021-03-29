using Microsoft.Boogie;

namespace ProofGeneration
{
    /// <summary>
    /// Used to desugar maps as a Boogie-to-Boogie transformation.
    /// </summary>
    public class MapDesugaring
    {
        /// <summary>
        /// Desugar maps in the input program
        /// </summary>
        /// <param name="p">Input program: Has to have been type-checked</param>
        /// <returns>Program without maps</returns>
        public static Program DesugarMaps(Program p)
        {
            //We first record the map types with the goal of producing less general types. For instance, the most general abstraction
            //of <T>[ref, Field T]T is <T>[A, Field T]T where A is a free type parameter. However, if in the program there is only one
            //possible type that is a specialization of its abstraction, then we can generate a more specialized abstraction.

            var mapRecordVisitor = new MapRecordVisitor();
            var mapAbstractionBuilder = mapRecordVisitor.RecordTypes(p);
            var visitor = new MapDesugaringVisitor();
            Program desugaredProg = visitor.Desugar(p, mapAbstractionBuilder);

            return desugaredProg;
        }

    }

    public class MapRecordVisitor : ReadOnlyVisitor
    {
        private FrontendMapAbstractionBuilder mapBuilder;
        
        public FrontendMapAbstractionBuilder RecordTypes(Program p)
        {
            mapBuilder = new FrontendMapAbstractionBuilder();
            Visit(p);

            return mapBuilder.UniqueAbstractionBuilder();
        }
        
        public override MapType VisitMapType(MapType node)
        {
            mapBuilder.AbstractMapType(node);
            return node;
        }
    }
    
}