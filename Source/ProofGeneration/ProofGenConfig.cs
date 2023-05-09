namespace ProofGeneration
{
    /// <summary>
    ///     Used to indicate which proofs should be generated.
    /// </summary>
    public class ProofGenConfig
    {
        private bool _generateAstCfgE2E;
        private bool _generateCfgDagE2E;
        private bool _generatePassifE2E;
        private bool _generateVcE2E;
        private bool _generateAstCfgProof;
        private bool _generateCfgDagProof;
        private bool _generatePassifProof;
        private bool _generateVcProof;

        public ProofGenConfig AllOptionsEnabled()
        {
            _generateAstCfgE2E = true;
            _generateCfgDagE2E = true;
            _generatePassifE2E = true;
            _generateVcE2E = true;
            _generateAstCfgProof = true;
            _generateCfgDagProof = true;
            _generatePassifProof = true;
            _generateVcProof = true;
            return this;
        }
        
        /*
            _proofGenConfig.GeneratePassifE2E = _proofGenConfig.GenerateVcProof && _proofGenConfig.GenerateVcE2E && _proofGenConfig.GeneratePassifProof;
            _proofGenConfig.GenerateCfgDagE2E = _proofGenConfig.GeneratePassifE2E && _proofGenConfig.GenerateCfgDagProof;
            _proofGenConfig.GenerateAstCfgE2E = _proofGenConfig.GenerateCfgDagE2E && _proofGenConfig.GenerateAstCfgProof;

            _proofGenConfig.GenerateBeforeAstCfgProg = _proofGenConfig.GenerateAstCfgProof;
            _proofGenConfig.GenerateUnoptimizedCfgProg = proofGenInfo.GetOptimizationsFlag() && _proofGenConfig.GenerateAstCfgProof;
            _proofGenConfig.GenerateBeforeCfgDagProg = (proofGenInfo.GetOptimizationsFlag() &&  _proofGenConfig.GenerateCfgDagProof) || 
                                                       (!proofGenInfo.GetOptimizationsFlag() && (_proofGenConfig.GenerateAstCfgProof || _proofGenConfig.GenerateCfgDagProof));
            _proofGenConfig.GenerateBeforePassifProg = _proofGenConfig.GenerateCfgDagProof || _proofGenConfig.GeneratePassifProof; 
            _proofGenConfig.GeneratePassifiedProg = _proofGenConfig.GeneratePassifProof || _proofGenConfig.GenerateVcProof;
        */
        public bool GenerateAstCfgE2E => _generateAstCfgE2E && GenerateAstCfgProof;

        public ProofGenConfig SetAstCfgE2E(bool flag)
        {
          _generateAstCfgE2E = flag;
          return this;
        }

        public bool GenerateCfgDagE2E => _generateCfgDagE2E && GenerateCfgDagProof;
        public ProofGenConfig SetCfgDagE2E(bool flag)
        {
          _generateCfgDagE2E = flag;
          return this;
        }

        public bool GeneratePassifE2E => _generatePassifE2E && GeneratePassifProof && GenerateVcE2E;

        public ProofGenConfig SetPassifE2E(bool flag)
        {
          _generatePassifE2E = flag;
          return this;
        }

        public bool GenerateVcE2E => _generateVcE2E && GenerateVcProof;
        
        public ProofGenConfig SetVcE2E(bool flag)
        {
          _generateVcE2E = flag;
          return this;
        }

        public bool GenerateAstCfgProof => _generateAstCfgProof;
        public ProofGenConfig SetAstCfgProof(bool flag)
        {
          _generateAstCfgProof = flag;
          return this;
        }

        public bool GenerateCfgDagProof => _generateCfgDagProof;
        public ProofGenConfig SetCfgDagProof(bool flag)
        {
          _generateCfgDagProof = flag;
          return this;
        }

        public bool GeneratePassifProof => _generatePassifProof;
        public ProofGenConfig SetPassifProof(bool flag)
        {
          _generatePassifProof = flag;
          return this;
        }

        public bool GenerateVcProof => _generateVcProof;
        
        public ProofGenConfig SetVcProof(bool flag)
        {
          _generateVcProof = flag;
          return this;
        }

        /** Program Generation Getters */
        
        public bool GenerateBeforeAstCfgProg => GenerateAstCfgProof;

        public bool GenerateUnoptimizedCfgProg(bool optimizationsHaveAnEffect)
        {
          return optimizationsHaveAnEffect && GenerateAstCfgProof;
        }

        public bool GenerateBeforeCfgDagProg(bool optimizationsHaveAnEffect)
        {
          return GenerateCfgDagProof || (optimizationsHaveAnEffect && GenerateAstCfgProof);
        }

        public bool GenerateBeforePassiveProg => GenerateCfgDagProof || GeneratePassifProof;
        public bool GeneratePassifiedProg => GeneratePassifProof || GenerateVcProof;
    }
}