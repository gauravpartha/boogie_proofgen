using System.Diagnostics.Contracts;
using Microsoft.Boogie;
using Microsoft.Boogie.TypeErasure;
using Microsoft.Boogie.VCExprAST;

namespace ProofGeneration.VCProofGen
{
    public class TypePremiseEraserFactory 
    {
        private readonly VCExpressionGenerator _vcExprGen;
        private readonly Boogie2VCExprTranslator _vcTranslator;
        
        public TypePremiseEraserFactory(VCExpressionGenerator vcExprGen, Boogie2VCExprTranslator vcTranslator)
        {
            _vcExprGen = vcExprGen;
            _vcTranslator = vcTranslator;
        }

        public TypePremiseEraserProvider NewEraser(bool extractTypeArgs=true)
        {
            return new TypePremiseEraserProvider(_vcExprGen, _vcTranslator, extractTypeArgs);
        }
    }

    public class TypePremiseEraserProvider
    {
        public TypeAxiomBuilderPremisses AxiomBuilder { get; }
        public TypeEraserPremisses Eraser { get;  }
        private readonly VCExpressionGenerator _vcExprGen;
        private readonly Boogie2VCExprTranslator _vcTranslator;

        public TypePremiseEraserProvider(VCExpressionGenerator vcExprGen, Boogie2VCExprTranslator vcTranslator, bool extractTypeArgs=true)
        {
            _vcExprGen = vcExprGen;
            AxiomBuilder = new TypeAxiomBuilderPremisses(vcExprGen);
            AxiomBuilder.Setup();
            Eraser = new TypeEraserPremisses(AxiomBuilder, vcExprGen, extractTypeArgs);
            _vcTranslator = vcTranslator;
        }

        public VCExpr TranslateAndErase(Expr e)
        {
            return EraseVC(_vcTranslator.Translate(e));
        }
        public VCExpr EraseVC(VCExpr vc)
        {
              VCExpr exprWithoutTypes = Eraser.Erase(vc, 1);
              LetBindingSorter letSorter = new LetBindingSorter(_vcExprGen);
              Contract.Assert(letSorter != null);
              return letSorter.Mutate(exprWithoutTypes, true);
        }
    }
}