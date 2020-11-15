using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;

namespace Microsoft.Boogie.ProofGen
{
    /// <summary>
    /// Class for axioms that appear in the VC.
    /// </summary>
    public abstract class VCAxiomInfo
    {
        public VCExpr Expr { get; }
            
        public VCAxiomInfo(VCExpr expr)
        {
            this.Expr = expr;
        }
    }

    public class VcBoogieAxiomInfo : VCAxiomInfo
    {
        public Axiom Axiom { get; }
        
        public VcBoogieAxiomInfo(VCExpr expr, Axiom axiom) : base(expr)
        {
            this.Axiom = axiom;
        }
    }
    
    public class VcFunctionAxiomInfo : VCAxiomInfo
    {
        public Function Function { get; }

        public VcFunctionAxiomInfo(VCExpr expr, Function function) : base(expr)
        {
            this.Function = function;
        }
    }

    public class VarAxiomInfo : VCAxiomInfo
    {
        public VCExprVar VcVar { get; }
        
        public VarAxiomInfo(VCExprVar vcVar, VCExpr expr) : base(expr)
        {
            this.VcVar = vcVar;
        }
    }

    public abstract class CtorAxiomInfo : VCAxiomInfo
    {
        public int CtorValue { get; }
        public CtorAxiomInfo(int ctorValue, VCExpr expr) : base(expr)
        {
            CtorValue = ctorValue;
        }
    }
    public class CtorBasicTypeAxiomInfo : CtorAxiomInfo
    {
        public Type Type { get; }
        public CtorBasicTypeAxiomInfo(Type type, int ctorValue, VCExpr expr) : base(ctorValue, expr)
        {
            Type = type;
        }
    }

    public class LeftInverseAxiomInfo : VCAxiomInfo
    {
        public TypeCtorDecl Decl { get; }
        public int projectedIdx { get;  }

        public LeftInverseAxiomInfo(TypeCtorDecl decl, int projectedIdx, VCExpr expr) : base(expr)
        {
            Decl = decl;
            this.projectedIdx = projectedIdx;
        }
    }
    
    public class CtorDeclAxiomInfo : CtorAxiomInfo 
    {
        public TypeCtorDecl Decl { get; }
        public CtorDeclAxiomInfo(TypeCtorDecl decl, int ctorValue, VCExpr expr) : base(ctorValue, expr)
        {
            Decl = decl;
        }
    }
    
    /// <summary>
    /// <see cref="BoxedOfUnboxed"/>: boxing followed by unboxing leads to the same value.
    /// <see cref="UnboxedOfBoxed"/>: unboxing followed by boxing leads to the same value, if the value has the correct type
    /// <see cref="TypeOfBoxed"/>: boxed values have the correct type
    /// </summary>
    public enum TypeCastKind
    {
        BoxedOfUnboxed, UnboxedOfBoxed, TypeOfBoxed
    }

    public class BasicTypeCastAxiomInfo : VCAxiomInfo
    {
        public Type Type { get; }

        public TypeCastKind CastKind { get; }

        public BasicTypeCastAxiomInfo(Type type, TypeCastKind castKind, VCExpr expr) : base(expr)
        {
            Type = type;
            CastKind = castKind;
        }
    }
}