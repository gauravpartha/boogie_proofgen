﻿using Microsoft.Boogie;
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

        public static LocaleDecl ConvertVC(VCExpr vc, VCExpressionGenerator gen, Program p, Implementation impl, CFGRepr cfg, out VCInstantiation vcinst)
        {
            VCExpr vcNoLabels = VCExprLabelRemover.RemoveLabels(vc, gen);
            VCExprLet vcNoLabelLet = vcNoLabels as VCExprLet;
            Contract.Assert(vcNoLabelLet != null);

            IList<Tuple<TermIdent, TypeIsa>> varsInVC = GetVarsInVC(p, impl, out IList<NamedDeclaration> holeSpec);

            IDictionary<Block, VCExpr> blockToVC = VCBlockExtractor.BlockToVCMapping(vcNoLabelLet, cfg);

            IDictionary<Block, DefDecl> blockToVCExpr = VCBlockToIsaTranslator.IsaDefsFromVC(blockToVC, cfg, impl.InParams, impl.LocVars);

            //order vc definitions of blocks in correct order
            IList<OuterDecl> vcBlockDefs = new List<OuterDecl>();

            foreach(var block in cfg.GetBlocksBackwards())
            {
                vcBlockDefs.Add(blockToVCExpr[block]);
            }

            LocaleDecl locale = new LocaleDecl("vc", new ContextElem(varsInVC, new List<Term>()), vcBlockDefs);



            vcinst = new VCInstantiation(blockToVCExpr, holeSpec, GetActiveDeclsPerBlock(blockToVC, holeSpec, cfg), locale.name);

            return locale;
        }

        //no global variables for now
        private static IList<Tuple<TermIdent, TypeIsa>> GetVarsInVC(Program p, Implementation impl, out IList<NamedDeclaration> holeSpec)
        {
            var pureTyIsaTransformer = new PureTyIsaTransformer();

            var result = new List<Tuple<TermIdent, TypeIsa>>();
            holeSpec = new List<NamedDeclaration>(); 

            foreach(Variable v in impl.InParams.Concat(impl.LocVars))
            {
                holeSpec.Add(v);
                result.Add(Tuple.Create(IsaCommonTerms.TermIdentFromName(v.Name), pureTyIsaTransformer.Translate(v.TypedIdent.Type)));                
            }            

            foreach(Function f in p.Functions)  {
                holeSpec.Add(f);
                IList<TypeIsa> types = f.InParams.Select(v => pureTyIsaTransformer.Translate(v.TypedIdent.Type)).ToList();
                

                TypeIsa retType = pureTyIsaTransformer.Translate(f.OutParams[0].TypedIdent.Type);
                types.Add(retType);

                TypeIsa funType = types.Reverse().Aggregate((res, arg) => new ArrowType(arg, res));
                result.Add(Tuple.Create(IsaCommonTerms.TermIdentFromName(f.Name), funType));
            }

            //TODO better interface
            return result;
        }

        private static IDictionary<Block, ISet<NamedDeclaration>> GetActiveDeclsPerBlock(
            IDictionary<Block, VCExpr> blockToVC, 
            IList<NamedDeclaration> decls, 
            CFGRepr cfg)
        {
            var blockToDecls = new Dictionary<Block, ISet<NamedDeclaration>>();

            var nameToDecl = new Dictionary<string, NamedDeclaration>();
            foreach (var decl in decls) {
                nameToDecl.Add(decl.Name, decl);
            }
     
            var declCollector = new VCExprDeclCollector();

            foreach (Block b in cfg.GetBlocksBackwards())
            {
                ISet<NamedDeclaration> bDecls = declCollector.CollectNamedDeclarations(blockToVC[b], nameToDecl);
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
