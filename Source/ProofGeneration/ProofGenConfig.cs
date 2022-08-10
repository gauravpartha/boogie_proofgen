namespace ProofGeneration
{
    /// <summary>
    ///     Used to indicate which proofs should be generated.
    /// </summary>
    public class ProofGenConfig
    {
        public ProofGenConfig(
            bool generateAstToCfg,
            bool generateCfgDagE2E,
            bool generatePassifE2E,
            bool generateVcE2E
        )
        {
            GenerateAstToCfg = generateAstToCfg;
            GenerateCfgDagE2E = generateCfgDagE2E;
            GeneratePassifE2E = generatePassifE2E;
            GenerateVcE2E = generateVcE2E;
        }
        
        public bool GenerateAstToCfg { get; }
        public bool GenerateCfgDagE2E { get; }
        public bool GeneratePassifE2E { get; }
        public bool GenerateVcE2E { get; }
    }
}