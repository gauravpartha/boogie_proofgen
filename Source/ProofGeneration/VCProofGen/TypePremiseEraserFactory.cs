using System.Collections;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
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

        /// <summary>
        /// Erases the types in <paramref name="vc"/>.
        /// Note that this has a side-effect on <paramref name="vc"/>..
        /// </summary>
        public VCExpr EraseVC(VCExpr vc)
        {
              VCExpr exprWithoutTypes = Eraser.Erase(vc, -1);
              LetBindingSorter letSorter = new LetBindingSorter(_vcExprGen);
              Contract.Assert(letSorter != null);
              return letSorter.Mutate(exprWithoutTypes, true);
        }

        public VCExpr BestTypeVarExtractor(
            TypeVariable typeVar, 
            VCExprVar dummyVariable,
            List<Type> vcFunctionValueTypes, 
            List<VCExprVar> vcFunctionValueArgs)
        {
            var varBindings = new Dictionary<VCExprVar, VCExprVar>();
            var typeVarBindings = new Dictionary<TypeVariable, VCExpr>();
            typeVarBindings.Add(typeVar, dummyVariable);
            VariableBindings b = new VariableBindings(varBindings, typeVarBindings);
            List<VCExprLetBinding> binding = AxiomBuilder.BestTypeVarExtractors(new List<TypeVariable>() {typeVar}, vcFunctionValueTypes, vcFunctionValueArgs, b);
            return binding[0].E;
        }
    }
}