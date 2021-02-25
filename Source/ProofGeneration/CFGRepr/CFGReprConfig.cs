using System;
using Microsoft.Boogie;

namespace ProofGeneration.CFGRepresentation
{
    public class CFGReprConfig
    {
        public bool GenerateBlockCopy { get; }
        public bool IsAcyclic { get; }
        public bool DesugarCalls { get; } 
        public Predicate<Cmd> DeepCopyCmdPred { get; }

        public CFGReprConfig(bool generateBlockCopy, bool isAcyclic, bool desugarCalls,
            Predicate<Cmd> deepCopyCmdPred)
        {
            GenerateBlockCopy = generateBlockCopy;
            IsAcyclic = isAcyclic;
            DesugarCalls = desugarCalls;
            DeepCopyCmdPred = deepCopyCmdPred;
        }
    }
    
    /// <summary>
    /// Builder for <see cref="CFGReprConfig"/>.
    /// Defaults: no block copy, not acyclic, no desugaring of calls, no copying of commands
    /// </summary>
    public class CFGReprConfigBuilder
    {
        private bool _generateBlockCopy = false;
        private bool _isAcyclic = false;
        private bool _desugarCalls = false;
        private Predicate<Cmd> _deepCopyCmdPred = cmd => false;

        public CFGReprConfig Build()
        {
            return new CFGReprConfig(_generateBlockCopy, _isAcyclic, _desugarCalls, _deepCopyCmdPred);
        }

        public CFGReprConfigBuilder SetBlockCopy(bool genBlockCopy)
        {
            _generateBlockCopy = genBlockCopy;
            return this;
        }

        public CFGReprConfigBuilder SetIsAcyclic(bool isAcylic)
        {
            _isAcyclic = isAcylic;
            return this;
        }

        public CFGReprConfigBuilder SetDesugarCalls(bool desugarCalls)
        {
            _desugarCalls = desugarCalls;
            return this;
        }
        
        public CFGReprConfigBuilder SetDeepCopyPredCmd(Predicate<Cmd> deepCopyCmdPred)
        {
            _deepCopyCmdPred = deepCopyCmdPred;
            return this;
        }
    }
}