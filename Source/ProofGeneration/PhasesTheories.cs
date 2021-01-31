using Microsoft.Boogie;

namespace ProofGeneration
{
    public class PhasesTheories
    {

        public enum Phase
        {
            Vc, Passification, CfgToDag
        }

        private readonly string vcPhaseTheoryName;
        private readonly string passificationTheoryName;
        private readonly string cfgToDagTheoryName;


        public PhasesTheories(string prefix)
        {
            vcPhaseTheoryName = prefix + "_vcphase_proof";
            passificationTheoryName = prefix + "_passification_proof";
            cfgToDagTheoryName = prefix + "_cfgtodag_proof";
        }

        public string TheoryName(Phase phase)
        {
            switch (phase)
            {
                case Phase.Vc:
                    return vcPhaseTheoryName;
                case Phase.Passification:
                    return passificationTheoryName;
                case Phase.CfgToDag:
                    return cfgToDagTheoryName;
                default:
                    throw new ProofGenUnexpectedStateException("unknown phase");
            }
        }

        public static string LocalEndToEndName()
        {
            return "end_to_end";
        }

        public string EndToEndLemmaName(Phase phase, bool qualify)
        {
            //TODO: don't hardcode "glue_proof"
            var localName = phase == Phase.Passification ? "glue_proof." + LocalEndToEndName() : LocalEndToEndName();
            return MaybeQualifiedName(TheoryName(phase), localName, qualify);
        }

        private string MaybeQualifiedName(string theory, string name, bool qualify)
        {
            return (qualify ? theory + "." + name : name);
        }

    }
}