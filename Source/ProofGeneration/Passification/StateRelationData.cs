using System.Collections.Generic;
using Isabelle.Ast;
using Microsoft.Boogie;

namespace ProofGeneration.Passification
{
    /// <summary>
    ///     Stores Data representing a state relation for the passification phase, which can be referred to by
    ///     <see cref="StateRel" /> and which is defined in terms of the association list <see cref="StateRelList" /> whose
    ///     order of keys is given by <see cref="VarsMapped" />.
    ///     <see cref="VarToLookupLemma" /> maps each variable in the domain of the relation to its corresponding lookup and
    ///     lemma
    /// </summary>
    public class StateRelationData
    {
        public StateRelationData(
            IDictionary<Variable, LemmaDecl> varToLookupLemma,
            IList<Variable> varsMapped,
            TermIdent stateRel,
            TermIdent stateRelList,
            string allLemmasName
        )
        {
            VarToLookupLemma = varToLookupLemma;
            VarsMapped = varsMapped;
            StateRel = stateRel;
            StateRelList = stateRelList;
            AllLemmasName = allLemmasName;
        }

        public IDictionary<Variable, LemmaDecl> VarToLookupLemma { get; }
        public IList<Variable> VarsMapped { get; }
        public TermIdent StateRel { get; }
        public TermIdent StateRelList { get; }

        public string AllLemmasName { get; }
    }
}