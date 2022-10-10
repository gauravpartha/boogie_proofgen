namespace ProofGeneration
{
    /// <summary>
    ///     Used to indicate which proofs should be generated.
    /// </summary>
    public class ProofGenConfig
    {
        public ProofGenConfig(
            bool generateAstCfgE2E,
            bool generateCfgDagE2E,
            bool generatePassifE2E,
            bool generateVcE2E
        )
        {
            GenerateAstCfgE2E = generateAstCfgE2E;
            GenerateCfgDagE2E = generateCfgDagE2E;
            GeneratePassifE2E = generatePassifE2E;
            GenerateVcE2E = generateVcE2E;
        }
        
        public bool GenerateAstCfgE2E { get; set;  }
        public bool GenerateCfgDagE2E { get; set;  }
        public bool GeneratePassifE2E { get; set; }
        public bool GenerateVcE2E { get; }
    }
}