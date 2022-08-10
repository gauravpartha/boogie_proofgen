using System.Collections.Generic;
using Isabelle.Ast;
using Microsoft.Boogie;

namespace ProofGeneration.BoogieIsaInterface
{
    public class IsaBlockInfo
    {
        private readonly string theoryName;

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

        public IDictionary<Block, int> BlockIds { get; }
        public IDictionary<Block, OuterDecl> BlockCmdsDefs { get; }

        public IDictionary<Block, LemmaDecl> BlockOutEdgesLemmas { get; }

        public IDictionary<Block, LemmaDecl> BlockCmdsLemmas { get; }
        public string getTheoryName() { return theoryName; }

        public string CmdsQualifiedName(Block b)
        {
            return QualifiedName(BlockCmdsDefs[b]);
        }

        public string OutEdgesMembershipLemma(Block b)
        {
            return QualifiedName(BlockOutEdgesLemmas[b]);
        }

        public string BlockCmdsMembershipLemma(Block b)
        {
            return QualifiedName(BlockCmdsLemmas[b]);
        }

        private string QualifiedName(OuterDecl decl)
        {
            return theoryName + "." + decl.Name;
        }
    }
    
    public class IsaBigBlockInfo
    {
        //private readonly string theoryName;

        public IsaBigBlockInfo(
          string theoryName,
          IDictionary<BigBlock, int> bigblockIds,
          IDictionary<BigBlock, IList<OuterDecl>> bigblockDefs
        )
        {
          TheoryName = theoryName;
          BigBlockIds = bigblockIds;
          BigBlockDefs = bigblockDefs;
        }

        public IDictionary<BigBlock, int> BigBlockIds { get; }
        public IDictionary<BigBlock, IList<OuterDecl>> BigBlockDefs { get; }
        public string TheoryName { get; }

        public IList<string> CmdsQualifiedName(BigBlock b)
        {
          return QualifiedName(BigBlockDefs[b]);
        }
        
        private IList<string> QualifiedName(IList<OuterDecl> decls)
        {
          IList<string> names = new List<string>();
          foreach (var decl in decls)
          {
            names.Add(TheoryName + "." + decl.Name);
          }

          return names;
        }
    }
}