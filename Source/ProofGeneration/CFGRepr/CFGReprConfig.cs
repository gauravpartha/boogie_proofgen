using System;
using Microsoft.Boogie;

namespace ProofGeneration.CFGRepresentation
{
    public class CFGReprConfig
    {
        public CFGReprConfig(bool generateBlockCopy, bool isAcyclic, bool desugarCalls,
            Predicate<Cmd> deepCopyCmdPred)
        {
            GenerateBlockCopy = generateBlockCopy;
            IsAcyclic = isAcyclic;
            DesugarCalls = desugarCalls;
            DeepCopyCmdPred = deepCopyCmdPred;
        }

        public bool GenerateBlockCopy { get; }
        public bool IsAcyclic { get; }
        public bool DesugarCalls { get; }
        public Predicate<Cmd> DeepCopyCmdPred { get; }
    }

    /// <summary>
    ///     Builder for <see cref="CFGReprConfig" />.
    ///     Defaults: no block copy, not acyclic, no desugaring of calls, no copying of commands.
    /// </summary>
    public class CFGReprConfigBuilder
    {
        private Predicate<Cmd> _deepCopyCmdPred = cmd => false;
        private bool _desugarCalls;
        private bool _generateBlockCopy;
        private bool _isAcyclic;

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