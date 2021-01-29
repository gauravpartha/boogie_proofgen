using System;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Boogie.TypeErasure;
using Microsoft.Boogie.VCExprAST;
using Type = Microsoft.Boogie.Type;

namespace ProofGeneration.VCProofGen
{
    public class TypePremiseEraserFactory 
    {
        private readonly VCExpressionGenerator _vcExprGen;
        private readonly Boogie2VCExprTranslator _vcTranslator;
        public bool ProgramIsPolymorphic { get;  }

        /// <summary>
        /// Initializes a new instance of the <see cref="TypePremiseEraserFactory"/> class.
        /// This factory can be used to produce <see cref="TypePremiseEraserProvider"/> objects.
        /// </summary>
        /// <param name="vcExprGen"></param>
        /// <param name="vcTranslator"></param>
        /// <param name="programIsPolymorphic">Set to true iff the input program is polymorphic</param>
        public TypePremiseEraserFactory(
            VCExpressionGenerator vcExprGen, 
            Boogie2VCExprTranslator vcTranslator,
            bool programIsPolymorphic)
        {
            _vcExprGen = vcExprGen;
            _vcTranslator = vcTranslator;
            ProgramIsPolymorphic = programIsPolymorphic;
        }

        public TypePremiseEraserProvider NewEraser(bool extractTypeArgs=true)
        {
            return new TypePremiseEraserProvider(_vcExprGen, _vcTranslator, ProgramIsPolymorphic, extractTypeArgs);
        }
    }

    public class TypePremiseEraserProvider
    {
        /// <summary>
        /// non-null iff <see cref="ProgramIsPolymorphic"/> is true
        /// </summary>
        public TypeAxiomBuilderPremisses AxiomBuilder { get; }
        public TypeEraserPremisses Eraser { get;  }
        private readonly VCExpressionGenerator _vcExprGen;
        private readonly Boogie2VCExprTranslator _vcTranslator;
        public bool ProgramIsPolymorphic { get; }

        public TypePremiseEraserProvider(
            VCExpressionGenerator vcExprGen, 
            Boogie2VCExprTranslator vcTranslator, 
            bool programIsPolymorphic,
            bool extractTypeArgs=true)
        {
            _vcExprGen = vcExprGen;
            ProgramIsPolymorphic = programIsPolymorphic;
            if (programIsPolymorphic)
            {
                AxiomBuilder = new TypeAxiomBuilderPremisses(vcExprGen);
                AxiomBuilder.Setup();
            }
            else
            {
                AxiomBuilder = null;
            }
            Eraser = new TypeEraserPremisses(AxiomBuilder, vcExprGen, extractTypeArgs);
            _vcTranslator = vcTranslator;
        }

        public VCExpr TranslateAndErase(Expr e, int polarity = -1)
        {
            return EraseAndSortLet(_vcTranslator.Translate(e), polarity);
        }

        /// <summary>
        /// Erases the types in <paramref name="vc"/> (if program is polymorphic) and sort let binding.
        /// Note that this has a side-effect on <paramref name="vc"/>..
        /// </summary>
        public VCExpr EraseAndSortLet(VCExpr vc, int polarity = -1)
        {
            VCExpr exprWithoutTypes = ProgramIsPolymorphic ? Eraser.Erase(vc, polarity) : vc;
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