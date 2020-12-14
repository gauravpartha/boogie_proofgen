using System.Collections;
using System.Collections.Generic;
using Microsoft.Boogie;
using ProofGeneration.Isa;

namespace ProofGeneration.BoogieIsaInterface
{
    public class IsaBlockInfo
    {
        private readonly string theoryName; 
        
        public IDictionary<Block, int> BlockIds { get;  }
        public IDictionary<Block, OuterDecl> BlockCmdsDefs { get;  }
        
        public string CmdsQualifiedName(Block b)
        {
            return QualifiedName(BlockCmdsDefs[b]);
        }

        public IDictionary<Block, LemmaDecl> BlockOutEdgesLemmas { get; }
        
        public string OutEdgesMembershipLemma(Block b)
        {
            return QualifiedName(BlockOutEdgesLemmas[b]);
        }
        
        public IDictionary<Block, LemmaDecl> BlockCmdsLemmas { get; }

        public string BlockCmdsMembershipLemma(Block b)
        {
            return QualifiedName(BlockCmdsLemmas[b]);
        }
        
        private string QualifiedName(OuterDecl decl)
        {
            return theoryName + "." + decl.name;
        }
        public IsaBlockInfo(
            string theoryName,
            IDictionary<Block, int> blockIds,
            IDictionary<Block, OuterDecl> blockCmdsDefs,
            IDictionary<Block, LemmaDecl> blockOutEdgesLemmas,
            IDictionary<Block, LemmaDecl> blockCmdsLemmas
        )
        {
            this.theoryName = theoryName;
            BlockIds = blockIds;
            BlockCmdsDefs = blockCmdsDefs;
            BlockOutEdgesLemmas = blockOutEdgesLemmas;
            BlockCmdsLemmas = blockCmdsLemmas;
        }
    }
}