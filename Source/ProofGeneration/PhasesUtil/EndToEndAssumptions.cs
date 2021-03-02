using System.Collections.Generic;
using Isabelle.Ast;
using Isabelle.Util;
using ProofGeneration.BoogieIsaInterface;

namespace ProofGeneration.PhasesUtil
{
    public static class EndToEndAssumptions
    {
        public static Term NonEmptyTypesAssumption(Term absValTyMap)
        {
            Identifier bvType = new SimpleIdentifier("t");
            Term bvTypeTerm = new TermIdent(bvType);
            Identifier bvValue = new SimpleIdentifier("v");
            Term bvValueTerm = new TermIdent(bvValue);
            return TermQuantifier.MetaAll(new List<Identifier> {bvType},
                null,
                TermBinary.MetaImplies(IsaBoogieTerm.IsClosedType(bvTypeTerm),
                    TermQuantifier.Exists(new List<Identifier> {bvValue},
                        null,
                        TermBinary.Eq(IsaBoogieTerm.TypeToVal(absValTyMap, bvValueTerm), bvTypeTerm)
                    )));
        }

        public static Term ClosednessAssumption(Term absValTyMap)
        {
            Identifier boundVar = new SimpleIdentifier("v");
            return TermQuantifier.MetaAll(new List<Identifier> {boundVar},
                null,
                IsaBoogieTerm.IsClosedType(IsaBoogieTerm.TypeToVal(absValTyMap, new TermIdent(boundVar)))
            );
        }

        public static Term AxiomAssumption(BoogieContextIsa boogieContext, IProgramAccessor programAccessor,
            Term normalState)
        {
            return
                IsaBoogieTerm.AxiomAssm(
                    boogieContext.absValTyMap,
                    boogieContext.funContext,
                    IsaCommonTerms.TermIdentFromName(programAccessor.ConstsDecl()),
                    normalState,
                    programAccessor.AxiomsDecl()
                );
        }

        // TODO: adjust clients so don't require constsAndGlobals
        public static Term GlobalStateAssumption(BoogieContextIsa boogieContext, Term constsAndGlobals,
            Term normalState)
        {
            return
                IsaBoogieTerm.StateWf(
                    boogieContext.absValTyMap,
                    boogieContext.rtypeEnv,
                    constsAndGlobals,
                    IsaBoogieTerm.GlobalState(normalState));
        }


        // TODO: adjust clients so don't require paramsAndLocals
        public static Term LocalStateAssumption(BoogieContextIsa boogieContext, Term paramsAndLocals, Term normalState)
        {
            return
                IsaBoogieTerm.StateWf(
                    boogieContext.absValTyMap,
                    boogieContext.rtypeEnv,
                    paramsAndLocals,
                    IsaBoogieTerm.LocalState(normalState));
        }

        public static Term OldGlobalStateAssumption(Term normalState)
        {
            return TermBinary.Eq(IsaBoogieTerm.GlobalState(normalState), IsaBoogieTerm.OldGlobalState(normalState));
        }

        public static Term BinderStateEmpty(Term normalState)
        {
            return TermBinary.Eq(
                IsaBoogieTerm.BinderState(normalState),
                IsaCommonTerms.EmptyMap
            );
        }
    }
}