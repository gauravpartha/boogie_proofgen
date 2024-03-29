﻿using System;
using System.Collections.Generic;
using System.Linq;
using Isabelle.Ast;
using Isabelle.Util;
using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.Util;

namespace ProofGeneration.ProgramToVCProof
{
    public static class ContextHelper
    {
        public static IList<Tuple<TermIdent, TypeIsa>> GlobalFixedVariables(
            BoogieContextIsa boogieContext,
            IEnumerable<Function> functions,
            IEnumerable<Variable> variables,
            TermIdent normalInitState,
            IDictionary<Function, TermIdent> funToInterpMapping,
            IsaUniqueNamer uniqueNamer)
        {
            var absValType = new VarType("a");
            var pureTyIsaTransformer = LemmaHelper.ConretePureTyIsaTransformer(absValType);

            var result = new List<Tuple<TermIdent, TypeIsa>>
            {
                Tuple.Create((TermIdent) boogieContext.absValTyMap, IsaBoogieType.AbstractValueTyFunType(absValType)),
                Tuple.Create((TermIdent) boogieContext.varContext, IsaBoogieType.VarContextType()),
                Tuple.Create((TermIdent) boogieContext.funContext, IsaBoogieType.FunInterpType(absValType)),
                Tuple.Create(normalInitState, IsaBoogieType.NormalStateType(absValType))
            };

            foreach (var kv in funToInterpMapping)
            {
                result.Add(Tuple.Create(kv.Value, IsaBoogieType.BoogieFuncInterpType(absValType)));

                var boogieFun = kv.Key;
                //get untyped version, maybe should precompute this somewhere and re-use or get the data from the VC
                TypeUtil.SplitTypeParams(boogieFun.TypeParameters, boogieFun.InParams.Select(v => v.TypedIdent.Type),
                    out var explicitTypeVars, out _);

                var typeIsa = pureTyIsaTransformer.Translate(new Function(null, boogieFun.Name,
                    explicitTypeVars, boogieFun.InParams, boogieFun.OutParams[0]));
                result.Add(Tuple.Create(
                    IsaCommonTerms.TermIdentFromName(uniqueNamer.GetName(boogieFun, boogieFun.Name)), typeIsa));
            }

            foreach (var v in variables)
            {
                var typeIsa = pureTyIsaTransformer.Translate(v);
                result.Add(Tuple.Create(IsaCommonTerms.TermIdentFromName(uniqueNamer.GetName(v, v.Name)), typeIsa));
            }

            return result;
        }
    }
}