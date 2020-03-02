using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;
using ProofGeneration.CFGRepresentation;
using ProofGeneration.Isa;
using ProofGeneration.Util;
using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace ProofGeneration.VCProofGen
{
    class VCToIsaInterface
    {

        public static LocaleDecl ConvertVC(
            VCExpr vc, 
            VCExpressionGenerator gen, 
            Boogie2VCExprTranslator translator, 
            IEnumerable<Function> functions,
            IEnumerable<Variable> inParams,
            IEnumerable<Variable> localVars,
            CFGRepr cfg, 
            out VCInstantiation vcinst)
        {
            VCExprLet vcLet = vc as VCExprLet;
            Contract.Assert(vcLet != null);

            var uniqueNamer = new IsaUniqueNamer();

            IList<Tuple<TermIdent, TypeIsa>> varsInVC = GetVarsInVC(functions, inParams, localVars, translator, uniqueNamer, out IList<NamedDeclaration> holeSpec);

            IDictionary<Block, VCExpr> blockToVC = VCBlockExtractor.BlockToVCMapping(vcLet, cfg);

            var blockToIsaTranslator = new VCBlockToIsaTranslator(uniqueNamer);
            IDictionary<Block, DefDecl> blockToVCExpr = blockToIsaTranslator.IsaDefsFromVC(blockToVC, cfg, inParams, localVars);

            //order vc definitions of blocks in correct order
            IList<OuterDecl> vcOuterDecls = new List<OuterDecl>();

            foreach(var block in cfg.GetBlocksBackwards())
            {
                vcOuterDecls.Add(blockToVCExpr[block]);
            }

            IDictionary<VCExprVar, Variable> vcToBoogieVar = VCExprToBoogieVar(translator, holeSpec);

            //reason for using two references: cannot use out paramaters in lambda expressions
            vcinst = new VCInstantiation(blockToVCExpr, holeSpec, GetActiveDeclsPerBlock(blockToVC, vcToBoogieVar, holeSpec, cfg), "vc");
            var vcinstInternal = vcinst;

            var blah = cfg.GetBlocksForwards().Select(b => vcinstInternal.GetVCBlockNameRef(b, false) + "_def").Concat(" ");

            LemmaDecl vcCorrectLemma = new LemmaDecl("vc_correct",
                vcinstInternal.GetVCBlockRef(cfg.entry, false),
                new Proof(
                  new List<string>() {
                      "apply (simp only: " +
                      cfg.GetBlocksForwards().Select(b => vcinstInternal.GetVCBlockNameRef(b, false) + "_def").Concat(" ")
                      + ")",
                      "oops"
                  }
                ));

            vcOuterDecls.Add(vcCorrectLemma);

            return new LocaleDecl("vc", ContextElem.CreateWithFixedVars(varsInVC), vcOuterDecls);
        }

        private static IDictionary<VCExprVar, Variable> VCExprToBoogieVar(Boogie2VCExprTranslator translator, IList<NamedDeclaration> decls)
        {
            var vcToBoogieVar = new Dictionary<VCExprVar, Variable>();
            foreach(var decl in decls)
            {
                if(decl is Variable boogieVar)
                {
                    VCExprVar result = translator.TryLookupVariable(boogieVar);
                    if (result != null)
                        vcToBoogieVar.Add(result, boogieVar);
                }
            }

            return vcToBoogieVar;
        }

        //no global variables for now
        private static IList<Tuple<TermIdent, TypeIsa>> GetVarsInVC(
            IEnumerable<Function> functions, 
            IEnumerable<Variable> inParams,
            IEnumerable<Variable> localVars,
            Boogie2VCExprTranslator translator, 
            IsaUniqueNamer uniqueNamer, 
            out IList<NamedDeclaration> holeSpec)
        {
            var pureTyIsaTransformer = new PureTyIsaTransformer();

            var result = new List<Tuple<TermIdent, TypeIsa>>();
            holeSpec = new List<NamedDeclaration>(); 

            foreach(Variable v in inParams.Concat(localVars))
            {                

                VCExprVar vcVar = translator.TryLookupVariable(v);
                if(vcVar != null)
                {
                    holeSpec.Add(v);
                    result.Add(Tuple.Create(IsaCommonTerms.TermIdentFromName(uniqueNamer.GetName(vcVar, vcVar.Name)), pureTyIsaTransformer.TranslateDeclType(v)));
                }
            }       
        
            foreach(Function f in functions)  {
                holeSpec.Add(f);
                TypeIsa funType = pureTyIsaTransformer.TranslateDeclType(f);
                result.Add(Tuple.Create(IsaCommonTerms.TermIdentFromName(f.Name), funType));
            }

            return result;
        }

        private static IDictionary<Block, ISet<NamedDeclaration>> GetActiveDeclsPerBlock(
            IDictionary<Block, VCExpr> blockToVC,
            IDictionary<VCExprVar, Variable> vcToBoogieVar,
            IList<NamedDeclaration> decls, 
            CFGRepr cfg)
        {
            var blockToDecls = new Dictionary<Block, ISet<NamedDeclaration>>();
     
            var declCollector = new VCExprDeclCollector();

            foreach (Block b in cfg.GetBlocksBackwards())
            {
                ISet<NamedDeclaration> bDecls = declCollector.CollectNamedDeclarations(blockToVC[b], vcToBoogieVar);
                foreach(Block b_succ in cfg.GetSuccessorBlocks(b))
                {
                    //flattening
                    foreach (var sucDecl in blockToDecls[b_succ])
                    {
                        bDecls.Add(sucDecl);
                    }
                }

                blockToDecls[b] = bDecls;
            }

            return blockToDecls;
        }

    }
}
