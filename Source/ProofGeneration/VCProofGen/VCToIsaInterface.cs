using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;
using ProofGeneration.CFGRepresentation;
using ProofGeneration.Isa;
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
            Program p, 
            Implementation impl, 
            CFGRepr cfg, 
            out VCInstantiation vcinst)
        {
            VCExpr vcNoLabels = VCExprLabelRemover.RemoveLabels(vc, gen);
            VCExprLet vcNoLabelLet = vcNoLabels as VCExprLet;
            Contract.Assert(vcNoLabelLet != null);

            UniqueNamer uniqueNamer = new UniqueNamer();
            uniqueNamer.Spacer = "_";

            IList<Tuple<TermIdent, TypeIsa>> varsInVC = GetVarsInVC(p, impl, translator, uniqueNamer, out IList<NamedDeclaration> holeSpec);

            IDictionary<Block, VCExpr> blockToVC = VCBlockExtractor.BlockToVCMapping(vcNoLabelLet, cfg);

            var blockToIsaTranslator = new VCBlockToIsaTranslator(uniqueNamer);
            IDictionary<Block, DefDecl> blockToVCExpr = blockToIsaTranslator.IsaDefsFromVC(blockToVC, cfg, impl.InParams, impl.LocVars);

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

            return new LocaleDecl("vc", new ContextElem(varsInVC, new List<Term>()), vcOuterDecls);
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
        private static IList<Tuple<TermIdent, TypeIsa>> GetVarsInVC(Program p, Implementation impl, Boogie2VCExprTranslator translator, UniqueNamer uniqueNamer, out IList<NamedDeclaration> holeSpec)
        {
            var pureTyIsaTransformer = new PureTyIsaTransformer();

            var result = new List<Tuple<TermIdent, TypeIsa>>();
            holeSpec = new List<NamedDeclaration>(); 

            foreach(Variable v in impl.InParams.Concat(impl.LocVars))
            {                
                holeSpec.Add(v);

                VCExprVar vcVar = translator.TryLookupVariable(v);
                if(v == null)
                {
                    throw new ProofGenUnexpectedStateException<VCToIsaInterface>(typeof(VCToIsaInterface), "Could not find VC counterpart of Boogie variable.");
                }

                result.Add(Tuple.Create(IsaCommonTerms.TermIdentFromName(uniqueNamer.GetName(vcVar, vcVar.Name)), pureTyIsaTransformer.Translate(v.TypedIdent.Type)));                
            }            

            foreach(Function f in p.Functions)  {
                holeSpec.Add(f);
                IList<TypeIsa> types = f.InParams.Select(v => pureTyIsaTransformer.Translate(v.TypedIdent.Type)).ToList();
                

                TypeIsa retType = pureTyIsaTransformer.Translate(f.OutParams[0].TypedIdent.Type);
                types.Add(retType);

                TypeIsa funType = types.Reverse().Aggregate((res, arg) => new ArrowType(arg, res));
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
                foreach(Block b_succ in cfg.outgoingBlocks[b])
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
