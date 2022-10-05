using System.Collections.Generic;
using Isabelle.Ast;
using Microsoft.Boogie;

namespace ProofGeneration.BoogieIsaInterface
{
  public class IsaBigBlockInfo
    {
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