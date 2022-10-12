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
            bool generateVcE2E,
            bool generateAstCfgProof,
            bool generateCfgDagProof,
            bool generatePassifProof,
            bool generateVcProof
        )
        {
            GenerateAstCfgE2E = generateAstCfgE2E;
            GenerateCfgDagE2E = generateCfgDagE2E;
            GeneratePassifE2E = generatePassifE2E;
            GenerateVcE2E = generateVcE2E;
            
            GenerateAstCfgProof = generateAstCfgProof;
            GenerateCfgDagProof = generateCfgDagProof;
            GeneratePassifProof = generatePassifProof;
            GenerateVcProof = generateVcProof;
            
            
        }
        
        
        public bool GenerateAstCfgE2E { get; set;  }
        public bool GenerateCfgDagE2E { get; set;  }
        public bool GeneratePassifE2E { get; set; }
        public bool GenerateVcE2E { get; }
        
        public bool GenerateAstCfgProof { get; set;  }
        public bool GenerateCfgDagProof { get; set;  }
        public bool GeneratePassifProof { get; set; }
        public bool GenerateVcProof { get; }
    }
}