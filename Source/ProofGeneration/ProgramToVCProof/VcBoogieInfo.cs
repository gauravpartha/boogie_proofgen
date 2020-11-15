using System.Collections.Generic;
using Microsoft.Boogie;
using Microsoft.Boogie.ProofGen;
using Microsoft.Boogie.VCExprAST;
using ProofGeneration.VCProofGen;

namespace ProofGeneration.ProgramToVCProof
{
    public class VcBoogieInfo
    {
        public VCInstantiation<Block> VcInst { get; }
        public VCInstantiation<VCExpr> VcInstAxiom { get; }
        public IEnumerable<VCExpr> VcAxioms { get; }
        public IEnumerable<VCAxiomInfo> VcAxiomsInfo { get; }
        
        public VcBoogieInfo(
            VCInstantiation<Block> vcinst,
            VCInstantiation<VCExpr> vcInstAxiom,
            IEnumerable<VCExpr> vcAxioms,
            IEnumerable<VCAxiomInfo> vcAxiomsInfo)
        {
            this.VcInst = vcinst;
            this.VcInstAxiom = vcInstAxiom;
            this.VcAxioms = vcAxioms;
            this.VcAxiomsInfo = vcAxiomsInfo;
        }
    }
}