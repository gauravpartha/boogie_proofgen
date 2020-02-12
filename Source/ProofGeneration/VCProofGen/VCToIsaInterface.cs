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

        public static LocaleDecl ConvertVC(VCExpr vc, VCExpressionGenerator gen, Program p, Implementation impl)
        {
            VCExpr vcNoLabels = VCExprLabelRemover.RemoveLabels(vc, gen);
            VCExprLet vcNoLabelLet = vcNoLabels as VCExprLet;
            Contract.Assert(vcNoLabelLet != null);

            var cfg = CFGReprTransformer.getCFGRepresentation(impl);

            IDictionary<Block, DefDecl> blockToVCExpr = VCBlockToIsaTranslator.IsaDefsFromVC(vcNoLabelLet, cfg, impl.InParams, impl.LocVars);

            IList<Tuple<TermIdent, TypeIsa>> varsInVC = getVarsInVC(p, impl);

            //order vc definitions of blocks in correct order
            IList<OuterDecl> vcBlockDefs = new List<OuterDecl>();

            foreach(var block in cfg.GetBlocksBackwards())
            {
                vcBlockDefs.Add(blockToVCExpr[block]);
            }

            LocaleDecl locale = new LocaleDecl("vc", varsInVC, vcBlockDefs);
            return locale;
        }

        //order: parameters, local variables, functions (no global variables for now)
        private static IList<Tuple<TermIdent, TypeIsa>> getVarsInVC(Program p, Implementation impl)
        {
            var pureTyIsaTransformer = new PureTyIsaTransformer();

            var result = new List<Tuple<TermIdent, TypeIsa>>();

            foreach(Variable v in impl.InParams.Concat(impl.LocVars))
            {
                result.Add(Tuple.Create(IsaCommonTerms.TermIdentFromName(v.Name), pureTyIsaTransformer.Translate(v.TypedIdent.Type)));
            }

            foreach(Function f in p.Functions)  {
                IList<TypeIsa> types = f.InParams.Select(v => pureTyIsaTransformer.Translate(v.TypedIdent.Type)).ToList();
                

                TypeIsa retType = pureTyIsaTransformer.Translate(f.OutParams[0].TypedIdent.Type);
                types.Add(retType);

                TypeIsa funType = types.Reverse().Aggregate((res, arg) => new ArrowType(arg, res));
                result.Add(Tuple.Create(IsaCommonTerms.TermIdentFromName(f.Name), funType));
            }

            //TODO better interface
            return result;
        }

    }
}
