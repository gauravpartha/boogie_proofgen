namespace ProofGeneration
{
    /// <summary>
    ///     Used to indicate which proofs should be generated.
    /// </summary>
    public class ProofGenConfig
    {
        public ProofGenConfig(
            bool generateBeforeAstCfgProg,
            bool generateUnoptimizedCfgProg,
            bool generateBeforeCfgDagProg,
            bool generateBeforePassifProg,
            bool generatePassifiedProg,
            bool generateAstCfgE2E,
            bool generateCfgDagE2E,
            bool generatePassifE2E,
            bool generateVcE2E,
            bool generateAstCfgProof,
            bool generateCfgDagProof,
            bool generatePassifProof,
            bool generateVcProof
        )
        {
            GenerateBeforeAstCfgProg = generateBeforeAstCfgProg;
            GenerateUnoptimizedCfgProg = generateUnoptimizedCfgProg;
            GenerateBeforeCfgDagProg = generateBeforeCfgDagProg;
            GenerateBeforePassifProg = generateBeforePassifProg;
            GeneratePassifiedProg = generatePassifiedProg;
          
            GenerateAstCfgE2E = generateAstCfgE2E;
            GenerateCfgDagE2E = generateCfgDagE2E;
            GeneratePassifE2E = generatePassifE2E;
            GenerateVcE2E = generateVcE2E;
            
            GenerateAstCfgProof = generateAstCfgProof;
            GenerateCfgDagProof = generateCfgDagProof;
            GeneratePassifProof = generatePassifProof;
            GenerateVcProof = generateVcProof;
        }
        
        public bool GenerateBeforeAstCfgProg { get; set; }
        public bool GenerateUnoptimizedCfgProg { get; set; }
        public bool GenerateBeforeCfgDagProg { get; set; }
        public bool GenerateBeforePassifProg { get; set; }
        public bool GeneratePassifiedProg { get; set; }

        public bool GenerateAstCfgE2E { get; set; }
        public bool GenerateCfgDagE2E { get; set; }
        public bool GeneratePassifE2E { get; set; }
        public bool GenerateVcE2E { get; }
        
        public bool GenerateAstCfgProof { get; set; }
        public bool GenerateCfgDagProof { get; set; }
        public bool GeneratePassifProof { get; set; }
        public bool GenerateVcProof { get; }
    }
}