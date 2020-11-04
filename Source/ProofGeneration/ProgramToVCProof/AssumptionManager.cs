using System;
using System.Collections.Generic;
using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.BoogieIsaInterface.VariableTranslation;
using ProofGeneration.Isa;

namespace ProofGeneration.ProgramToVCProof
{
    public class AssumptionManager
    {
        private readonly IDictionary<object, List<string>> _assumptionLabelMap = new Dictionary<object, List<string>>();
        private readonly IVariableTranslationFactory _factory;

        private const string LabelPrefix = "G";
        private int _counter = 0;
        
        public enum SpecialAssumptionsKind
        {
           TypeValClosed 
        }

        public AssumptionManager(IEnumerable<Function> functions, IEnumerable<Variable> variables, IVariableTranslationFactory factory)
        {
            _factory = factory;
            foreach (var f in functions)
            {
                RecordAssumptionLabel(f);
            }

            foreach (var v in variables)
            {
                RecordAssumptionLabel(v);
            }
            
            RecordAssumptionLabel(SpecialAssumptionsKind.TypeValClosed);
        }

        private void RecordAssumptionLabel(Object obj)
        {
            var newLabel = NextLabel();
            var result = new List<string> {newLabel};
            if (obj is Function f || obj is Variable v && !TypeUtil.IsPrimitive(v.TypedIdent.Type))
            {
                //create another label, since two assumptions are used 
                string anotherNewLabel = NextLabel();
                result.Add(anotherNewLabel);
            }

            _assumptionLabelMap.Add(obj, result);
        }        
        
        /// <summary> Retrieves labels for function context well-formedness assumption and
        /// function correspondence assumption.
        /// </summary>
        public void GetAssumptionLabel(Function f, out string funCtxtLabel, out string funCorresLabel)
        {
            var result = GetAssumptionLabelMain(f);
            funCtxtLabel = result[0];
            funCorresLabel = result[1];
        }
        
        /// <summary> Retrieves labels for the assumption that a state maps the variable to some value
        /// (<paramref name="stateVarLabel"/>) and the type of value that it is mapped to (<paramref name="varTypeLabel"/>)
        /// The latter may be null, since for primitive types the type information already included in the former. </summary>
        public void GetAssumptionLabel(Variable v, out string stateVarLabel, out string varTypeLabel)
        {
            var variableLabels = GetAssumptionLabelMain(v);
            stateVarLabel = variableLabels[0];
            if (variableLabels.Count == 2)
            {
                varTypeLabel = variableLabels[1];
            }

            varTypeLabel = null;
        }
        
        /// <summary> Retrieves label for assumption associated with <paramref name="assumptionKind"/>. </summary>
        public string GetAssumptionLabel(SpecialAssumptionsKind assumptionKind)
        {
            return GetAssumptionLabelMain(assumptionKind)[0];
        }

        private List<string> GetAssumptionLabelMain(object obj)
        {
            return _assumptionLabelMap[obj];
        }

        /// <summary>The returned list in-sync with <see cref="AllAssumptionLabels"/>.</summary>
        public IList<Term> AllAssumptions(
            IDictionary<Function, TermIdent> funInterpMapping,
            IDictionary<NamedDeclaration, Term> declToVCMapping, 
            Term state,
            BoogieContextIsa boogieContext,
            IVariableTranslation<Variable> varTranslation
            )
        {
            var assumptions = new List<Term>();
            foreach (var obj in _assumptionLabelMap.Keys)
            {
                if (obj is Function f)
                {
                    assumptions.Add(LemmaHelper.FunctionCtxtWfAssm(f, funInterpMapping, boogieContext)); 
                    assumptions.Add(LemmaHelper.FunctionVcCorresAssm(f, funInterpMapping, declToVCMapping, boogieContext));
                } else if (obj is Variable v)
                {
                    assumptions.Add(LemmaHelper.StateVariableAssumption(v,state, declToVCMapping, varTranslation));
                    if (!TypeUtil.IsPrimitive(v.TypedIdent.Type))
                    {
                        assumptions.Add(LemmaHelper.VariableTypeAssumption(
                            v,
                            declToVCMapping[v], 
                            new TypeIsaVisitor(_factory.CreateEmptyTranslation().TypeVarTranslation), 
                            boogieContext.absValTyMap));
                    }
                } else if (obj is SpecialAssumptionsKind kind)
                {
                    switch (kind)
                    {
                        case SpecialAssumptionsKind.TypeValClosed:
                            assumptions.Add(ClosednessAssumption());
                            break;
                        default:
                            throw new ArgumentOutOfRangeException();
                    }
                }
            }

            return assumptions;
        }
        
        ///<summary>Every type of a value is closed.</summary>
        private Term ClosednessAssumption()
        {
            Identifier boundVar = new SimpleIdentifier("v");
            Term absValTyMap = IsaCommonTerms.TermIdentFromName("A");
            return TermQuantifier.MetaAll(new List<Identifier>{boundVar},
                null,
                IsaBoogieTerm.IsClosedType(IsaBoogieTerm.TypeToVal(absValTyMap, new TermIdent(boundVar)))
            );
        }

        public IList<string> AllAssumptionLabels()
        {
            var assumptionLabels = new List<string>();
            foreach (var labels in _assumptionLabelMap.Values)
            {
                assumptionLabels.AddRange(labels);
            }

            return assumptionLabels;
        }

        private string NextLabel()
        {
            string newLabel = LabelPrefix + _counter;
            _counter++;
            return newLabel; 
        }
    }
}