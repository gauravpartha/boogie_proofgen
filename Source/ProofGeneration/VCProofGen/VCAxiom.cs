using System.Net;
using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;

namespace ProofGeneration.VCProofGen
{
    //class for axioms that appears in the VC
    public abstract class VCAxiom
    {
        public VCExpr Expr { get; }
            

        public VCAxiom(VCExpr expr)
        {
            this.Expr = expr;
        }
    }

    public class VCBoogieAxiom : VCAxiom
    {
        public Axiom Axiom { get; }
        
        public VCBoogieAxiom(VCExpr expr, Axiom axiom) : base(expr)
        {
            this.Axiom = axiom;
        }
    }

    public class VCFunctionAxiom : VCAxiom
    {
        public Function Function { get; }

        public VCFunctionAxiom(VCExpr expr, Function function) : base(expr)
        {
            this.Function = function;
        }
    }

    public class VCTypeConvAxiom : VCAxiom
    {
        public VCTypeConvAxiom(VCExpr expr) : base(expr)
        {
            
        }
    }

    public class CtorAxiom : VCAxiom
    {
        public CtorAxiom(VCExpr expr) : base(expr)
        {
            
        }
    }

    public class VCOtherAxiom : VCAxiom
    {
        public VCOtherAxiom(VCExpr expr) : base(expr)
        {
            
        }
    }
    
    
}