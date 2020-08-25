using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.CFGRepresentation;
using ProofGeneration.Isa;
using ProofGeneration.Util;
using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace ProofGeneration.VCProofGen
{
    class VCToIsaInterface
    {

        public static LocaleDecl ConvertVC(
            string localeName,
            VCExpr vc,
            IEnumerable<VCExpr> vcAxioms,
            IActiveDeclGenerator activeDeclGenerator,
            VCExpressionGenerator gen,
            Boogie2VCExprTranslator translator,
            BoogieMethodData methodData,
            CFGRepr cfg,
            out VCInstantiation<Block> vcinst,
            out VCInstantiation<Axiom> vcinstAxiom)
        {
            VCExprLet vcLet = vc as VCExprLet;
            Contract.Assert(vcLet != null);

            var uniqueNamer = new IsaUniqueNamer();
            IDictionary<Block, VCExpr> blockToVC = VCBlockExtractor.BlockToVCMapping(vcLet, cfg);


            IDictionary<VCExprVar, Variable> vcToBoogieVar = VCExprToBoogieVar(translator, methodData.InParams.Union(methodData.Locals));
            IDictionary<Block, ISet<NamedDeclaration>> activeDeclsPerBlock = 
                activeDeclGenerator.GetActiveDeclsPerBlock(blockToVC, vcToBoogieVar, cfg, out IDictionary<Block, ISet<Variable>> blockToNewVars);

            IDictionary<Block, IList<NamedDeclaration>> activeDeclsPerBlockSorted =
                SortActiveDecls(activeDeclsPerBlock, methodData.Functions, translator, out IDictionary<Block, IList<VCExprVar>> activeVarsPerBlock);

            IDictionary<Block, IList<VCExprVar>> blockToNewVCVars = ConvertVariableToVCExpr(blockToNewVars, translator);

            var blockToIsaTranslator = new VCBlockToIsaTranslator(uniqueNamer);
            IDictionary<Block, DefDecl> blockToVCExpr = 
                blockToIsaTranslator.IsaDefsFromVC(blockToVC, activeVarsPerBlock, cfg, methodData, blockToNewVCVars);

            //add vc definitions of blocks in correct order
            IList<OuterDecl> vcOuterDecls = new List<OuterDecl>();

            foreach (var block in cfg.GetBlocksBackwards())
            {
                vcOuterDecls.Add(blockToVCExpr[block]);
            }

            //reason for using two references: cannot use out parameters in lambda expressions
            vcinst = new VCInstantiation<Block>(blockToVCExpr, activeDeclsPerBlockSorted, localeName);
            var vcinstInternal = vcinst;

            /*
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
            IDictionary<Axiom, ISet<NamedDeclaration>> activeDeclsPerAxiom = VCInstAxioms(methodData.Axioms, vcAxioms, vcToBoogieVar);
            IDictionary<Axiom, IList<NamedDeclaration>> activeDeclsPerAxiomSorted =
                 SortActiveDecls(activeDeclsPerAxiom, methodData.Functions, translator, out IDictionary<Axiom, IList<VCExprVar>> activeVarsPerAxiom);
            var axiomVCDefs = new List<DefDecl>();
            var axiomToDef = new Dictionary<Axiom, DefDecl>();
            var vcExprIsaTranslator = new VCExprToIsaTranslator(uniqueNamer);
            int axId = 0;
            void axiomsAction(Axiom ax, VCExpr vcAx)
            {
                IList<Term> args = activeVarsPerAxiom[ax].Select(v => vcExprIsaTranslator.Translate(v)).ToList();
                Term rhs = vcExprIsaTranslator.Translate(vcAx);

                DefDecl def = new DefDecl("vcax_"+axId, new Tuple<IList<Term>, Term>(args, rhs));
                axiomToDef.Add(ax, def);
                axId++;
            }
            BasicUtil.ZipDo(methodData.Axioms, vcAxioms, axiomsAction);
            vcinstAxiom = new VCInstantiation<Axiom>(axiomToDef, activeDeclsPerAxiomSorted, localeName);

            vcOuterDecls.AddRange(axiomToDef.Values);

            return new LocaleDecl(localeName, ContextElem.CreateWithFixedVars(GetVarsInVC(methodData.Functions, uniqueNamer)), vcOuterDecls);
        }

        private static Dictionary<T, IList<NamedDeclaration>>  SortActiveDecls<T>(
            IDictionary<T, ISet<NamedDeclaration>> activeDeclsPerBlock,
            IEnumerable<Function> functions,
            Boogie2VCExprTranslator translator,
            out IDictionary<T, IList<VCExprVar>> activeVarsPerBlock)
        {
            activeVarsPerBlock = new Dictionary<T, IList<VCExprVar>>();
            var activeDeclsPerBlockSorted = new Dictionary<T, IList<NamedDeclaration>>();

            foreach (KeyValuePair<T, ISet<NamedDeclaration>> kv in activeDeclsPerBlock)
            {
                var activeVars = kv.Value.Where(decl => decl is Variable);

                var activeVCVars = activeVars.Select(decl => { var vcVar = translator.TryLookupVariable((Variable)decl); Contract.Assert(vcVar != null); return vcVar; }).ToList();
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
                activeDeclsPerBlockSorted.Add(kv.Key, sortedDecls);
            }

            return activeDeclsPerBlockSorted;
        }

        private static IDictionary<Block, IList<VCExprVar>> ConvertVariableToVCExpr(IDictionary<Block, ISet<Variable>> dict, Boogie2VCExprTranslator translator)
        {
            if (dict == null)
                return null;

            var blockToNewVCVar = new Dictionary<Block, IList<VCExprVar>>();

            foreach (KeyValuePair<Block, ISet<Variable>> blockAndVars in dict)
            {
                IList<VCExprVar> newVCExprs = new List<VCExprVar>();
                foreach (Variable v in blockAndVars.Value)
                {
                    VCExprVar translatedVar = translator.TryLookupVariable(v);
                    if (translatedVar == null)
                    {
                        throw new ProofGenUnexpectedStateException(typeof(VCToIsaInterface), "Could not map Boogie variable to VC variable");
                    }
                    newVCExprs.Add(translatedVar);
                }
                blockToNewVCVar.Add(blockAndVars.Key, newVCExprs);
            }

            return blockToNewVCVar;
        }
   
        private static IDictionary<VCExprVar, Variable> VCExprToBoogieVar(Boogie2VCExprTranslator translator, IEnumerable<Variable> decls)
        {
            var vcToBoogieVar = new Dictionary<VCExprVar, Variable>();
            foreach (var decl in decls)
            {
                VCExprVar result = translator.TryLookupVariable(decl);
                if (result != null)
                    vcToBoogieVar.Add(result, decl);
            }

            return vcToBoogieVar;
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

        private static IDictionary<Axiom, ISet<NamedDeclaration>> VCInstAxioms(
            IEnumerable<Axiom> axioms, 
            IEnumerable<VCExpr> vcAxioms, 
            IDictionary<VCExprVar, Variable> vcToBoogieVar)
        {
            var result = new Dictionary<Axiom, ISet<NamedDeclaration>>();

            VCExprDeclCollector collector = new VCExprDeclCollector();
            void action(Axiom ax, VCExpr vc)
            {
                ISet<NamedDeclaration> decls = collector.CollectNamedDeclarations(vc, vcToBoogieVar);
                result.Add(ax, decls);
            }

            BasicUtil.ZipDo(axioms, vcAxioms, action);
            return result;
        }
    }
}
