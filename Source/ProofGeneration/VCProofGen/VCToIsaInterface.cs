using Microsoft.Boogie;
using Microsoft.Boogie.TypeErasure;
using Microsoft.Boogie.VCExprAST;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.CFGRepresentation;
using ProofGeneration.Isa;
using ProofGeneration.Util;
using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Boogie.ProofGen;

namespace ProofGeneration.VCProofGen
{
    class VCToIsaInterface
    {

        public static LocaleDecl ConvertVC(
            string localeName,
            VCExpr vc,
            IEnumerable<VCExpr> vcAxioms,
            IActiveDeclGenerator activeDeclGenerator,
            Boogie2VCExprTranslator translator,
            TypeAxiomBuilderPremisses axiomBuilder,
            BoogieMethodData methodData,
            CFGRepr cfg,
            out VCInstantiation<Block> vcinst,
            out VCInstantiation<VCExpr> vcinstAxiom,
            out IVCVarFunTranslator vcTranslator,
            out IEnumerable<Function> vcTypeFunctions)
        {
            VCExprLet vcLet = vc as VCExprLet;
            Contract.Assert(vcLet != null);

            var uniqueNamer = new IsaUniqueNamer();
            IDictionary<Block, VCExpr> blockToVC = VCBlockExtractor.BlockToVCMapping(vcLet, cfg);

            var declCollector = new VCFunDeclCollector();
            IDictionary<Function, Function> funToVCfun =
                (declCollector.CollectFunDeclarations(new List<VCExpr>() {vc}.Concat(vcAxioms), methodData.Functions));
            IVCVarFunTranslator varTranslator = new VCVarFunTranslator(methodData.AllVariables(), funToVCfun, translator, axiomBuilder);

            IDictionary<Block, ISet<NamedDeclaration>> activeDeclsPerBlock = 
                activeDeclGenerator.GetActiveDeclsPerBlock(blockToVC, varTranslator, cfg, out IDictionary<Block, ISet<Variable>> blockToNewVars);

            #region temporary: extend vc instantiation to support vc functions
            IList<Function> otherFunctions = new List<Function>();
            ISet<Function> otherFunctionsSet = new HashSet<Function>();

            foreach(NamedDeclaration decl in activeDeclsPerBlock[cfg.entry])
            {
                if (decl is Function fun && !varTranslator.TranslateBoogieFunction(fun, out _)) {
                    otherFunctions.Add(fun);
                    otherFunctionsSet.Add(fun);
                }
            }
            
            //also record functions that are used elswhere (type axiom related functions)
            VCExprDeclCollector collector = new VCExprDeclCollector();
            var vcExprs = vcAxioms.ToList();
            foreach(VCExpr ax in vcExprs)
            {
                var decls = collector.CollectNamedDeclarations(ax, varTranslator);
                foreach (var d in decls)
                {
                    if (d is Function fun && !varTranslator.TranslateBoogieFunction(fun, out _) &&
                        !otherFunctions.Contains(d) )
                    {
                        otherFunctions.Add(fun);
                    }
                }
            }
            #endregion

            IDictionary<Block, IList<NamedDeclaration>> activeDeclsPerBlockSorted =
                SortActiveDecls(activeDeclsPerBlock, methodData.Functions.Union(otherFunctions), varTranslator, out IDictionary<Block, IList<VCExprVar>> activeVarsPerBlock);

            IDictionary<Block, IList<VCExprVar>> blockToNewVCVars = ConvertVariableToVCExpr(blockToNewVars, varTranslator);

            var blockToIsaTranslator = new VCBlockToIsaTranslator(uniqueNamer);
            IDictionary<Block, DefDecl> blockToVCExpr = 
                blockToIsaTranslator.IsaDefsFromVC(blockToVC, activeVarsPerBlock, cfg, blockToNewVCVars);

            //add vc definitions of blocks in correct order
            IList<OuterDecl> vcOuterDecls = new List<OuterDecl>();

            foreach (var block in cfg.GetBlocksBackwards())
            {
                vcOuterDecls.Add(blockToVCExpr[block]);
            }

            vcinst = new VCInstantiation<Block>(blockToVCExpr, activeDeclsPerBlockSorted, localeName);

            /*
             *             
            //reason for using second reference: cannot use out parameters in lambda expressions
            var vcinstInternal = vcinst;

            LemmaDecl vcCorrectLemma = new LemmaDecl("vc_correct",
                new TermApp(vcinstInternal.GetVCObjRef(cfg.entry, false), 
                           activeVarsPerBlock[cfg.entry].Select(v => (Term) IsaCommonTerms.TermIdentFromName(uniqueNamer.GetName(v, v.Name))).ToList()),
                new Proof(
                  new List<string>() {
                      "apply (simp only: " +
                      cfg.GetBlocksForwards().Select(b => vcinstInternal.GetVCObjNameRef(b, false) + "_def").Concat(" ")
                      + ")",
                      "oops"
                  }
                ));

            vcOuterDecls.Add(vcCorrectLemma);
            */

            //axioms
            IDictionary<VCExpr, ISet<NamedDeclaration>> activeDeclsPerAxiom = VCInstAxioms(vcExprs, varTranslator);
            IDictionary<VCExpr, IList<NamedDeclaration>> activeDeclsPerAxiomSorted =
                 SortActiveDecls(activeDeclsPerAxiom, methodData.Functions.Union(otherFunctions), varTranslator, out IDictionary<VCExpr, IList<VCExprVar>> activeVarsPerAxiom);
            var axiomToDef = new Dictionary<VCExpr, DefDecl>();
            var vcExprIsaTranslator = new VCExprToIsaTranslator(uniqueNamer);

            if (activeDeclsPerAxiomSorted.Count != vcExprs.Count())
            {
                throw new ProofGenUnexpectedStateException(typeof(VCToIsaInterface), "count not in-sync");
            }
            
            int axId = 0;
            foreach(var vcAx in activeDeclsPerAxiomSorted.Keys)
            {
                IList<Term> args = activeVarsPerAxiom[vcAx].Select(v => vcExprIsaTranslator.Translate(v)).ToList();
                Term rhs = vcExprIsaTranslator.Translate(vcAx);

                DefDecl def = new DefDecl("vcax_"+axId, new Tuple<IList<Term>, Term>(args, rhs));
                axiomToDef.Add(vcAx, def);
                axId++;
            }

            vcinstAxiom = new VCInstantiation<VCExpr>(axiomToDef, activeDeclsPerAxiomSorted, localeName);

            vcOuterDecls.AddRange(axiomToDef.Values);

            var vcFunctions = methodData.Functions.
                Where(f => varTranslator.TranslateBoogieFunction(f, out Function result))
                .Select(f =>
                    {
                        if (varTranslator.TranslateBoogieFunction(f, out Function result))
                        {
                            return result;
                        }
                        else
                        {
                            throw new InvalidOperationException();
                        }
                    }).Union(otherFunctions);

            vcTranslator = varTranslator;
            vcTypeFunctions = otherFunctions;

            return new LocaleDecl(localeName, ContextElem.CreateWithFixedVars(GetVarsInVC(vcFunctions, uniqueNamer)), vcOuterDecls);
        }

        private static Dictionary<T, IList<NamedDeclaration>>  SortActiveDecls<T>(
            IDictionary<T, ISet<NamedDeclaration>> activeDeclsPerBlock,
            IEnumerable<Function> functions,
            IVCVarFunTranslator translator,
            out IDictionary<T, IList<VCExprVar>> activeVarsPerBlock)
        {
            activeVarsPerBlock = new Dictionary<T, IList<VCExprVar>>();
            var activeDeclsPerBlockSorted = new Dictionary<T, IList<NamedDeclaration>>();

            foreach (KeyValuePair<T, ISet<NamedDeclaration>> kv in activeDeclsPerBlock)
            {
                var activeVars = kv.Value.Where(decl => decl is Variable);
                var activeVCVars = activeVars.Select(decl => {
                    if (translator.TranslateBoogieVar((Variable)decl, out VCExprVar result))
                    {
                        return result;
                    } else
                    {
                        Contract.Assert(false);
                        return null;
                    }}).ToList();

                activeVarsPerBlock.Add(kv.Key, activeVCVars);

                var sortedDecls = new List<NamedDeclaration>();
                foreach (Function f in functions)
                {
                    if (kv.Value.Contains(f))
                    {
                        sortedDecls.Add(f);
                    }
                }
                sortedDecls.AddRange(activeVars);
                if(sortedDecls.Count() != kv.Value.Count)
                {
                    throw new ProofGenUnexpectedStateException(typeof(VCToIsaInterface), "did not capture all active declarations");
                }
                activeDeclsPerBlockSorted.Add(kv.Key, sortedDecls);
            }

            return activeDeclsPerBlockSorted;
        }

        private static IDictionary<Block, IList<VCExprVar>> ConvertVariableToVCExpr(IDictionary<Block, ISet<Variable>> dict, IVCVarFunTranslator translator)
        {
            if (dict == null)
                return null;

            var blockToNewVCVar = new Dictionary<Block, IList<VCExprVar>>();

            foreach (KeyValuePair<Block, ISet<Variable>> blockAndVars in dict)
            {
                IList<VCExprVar> newVCExprs = new List<VCExprVar>();
                foreach (Variable v in blockAndVars.Value)
                {
                    if (!translator.TranslateBoogieVar(v, out VCExprVar result))
                    {
                        throw new ProofGenUnexpectedStateException(typeof(VCToIsaInterface), "Could not map Boogie variable to VC variable");
                    }
                    newVCExprs.Add(result);
                }
                blockToNewVCVar.Add(blockAndVars.Key, newVCExprs);
            }

            return blockToNewVCVar;
        }
   
        private static IList<Tuple<TermIdent, TypeIsa>> GetVarsInVC(IEnumerable<Function> functions, IsaUniqueNamer uniqueNamer)
        {
            var pureTyIsaTransformer = new PureTyIsaTransformer();

            var result = new List<Tuple<TermIdent, TypeIsa>>();

            foreach (Function f in functions)
            {
                TypeIsa funType = pureTyIsaTransformer.Translate(f);
                result.Add(Tuple.Create(IsaCommonTerms.TermIdentFromName(f.Name), funType));
            }

            return result;
        }

        //length of vcAxioms is at least length n of axioms (direct correspondence between the first n elements of the
        //two lists)
        private static IDictionary<VCExpr, ISet<NamedDeclaration>> VCInstAxioms(
            IEnumerable<VCExpr> vcAxioms, 
            IVCVarFunTranslator translator)
        {
            var result = new Dictionary<VCExpr, ISet<NamedDeclaration>>();

            VCExprDeclCollector collector = new VCExprDeclCollector();
            foreach (var ax in vcAxioms)
            {
                var activeDecls = collector.CollectNamedDeclarations(ax, translator);
                result.Add(ax, activeDecls); 
            }
            
            return result;
        }
    }
}
