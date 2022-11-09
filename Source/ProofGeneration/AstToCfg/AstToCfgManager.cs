using System;
using System.Collections.Generic;
using System.Linq;
using Isabelle.Ast;
using Isabelle.Util;
using Microsoft.Boogie;
using ProofGeneration.ASTRepresentation;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.BoogieIsaInterface.VariableTranslation;
using ProofGeneration.CFGRepresentation;
using ProofGeneration.Util;

namespace ProofGeneration.AstToCfg
{
    internal class AstToCfgManager
    {
        public static Theory AstToCfgProof(
            string uniqueTheoryName,
            PhasesTheories phasesTheories,
            bool generateEndtoEnd,
            ProofGenConfig config,
            Term vcAssm,
            AstToCfgProofGenInfo proofGenInfo,
            ASTRepr beforeCfgAst,
            CFGRepr afterCfg,
            BoogieMethodData beforeCfgData,
            IDictionary<Block, Block> beforeDagOrigBlock,
            IDictionary<BigBlock, (Block,Expr,BranchIndicator)> mappingWithHints,
            IDictionary<BigBlock, Block> beforeToAfter,
            IProgramAccessor beforeCfgProgAccess,
            IProgramAccessor afterCfgProgAccess,
            IVariableTranslationFactory varFactory,
            MultiCmdIsaVisitor multiCmdIsaVisitor)
        {
            LemmaDecl entryLemma = null;

            var varContextName = "\\<Lambda>1";
            var varContextAbbrev = new AbbreviationDecl(
                varContextName,
                new Tuple<IList<Term>, Term>(new List<Term>(), beforeCfgProgAccess.VarContext())
            );

            var funContextWfName = "Wf_Fun";
            var astBoogieContext = new BoogieContextIsa(
                IsaCommonTerms.TermIdentFromName("A"),
                IsaCommonTerms.TermIdentFromName("M"),
                IsaCommonTerms.TermIdentFromName(varContextName),
                IsaCommonTerms.TermIdentFromName("\\<Gamma>"),
                IsaCommonTerms.EmptyList);
            var cfgBoogieContext = new BoogieContextIsa(
              IsaCommonTerms.TermIdentFromName("A"),
              IsaCommonTerms.TermIdentFromName("M"),
              IsaCommonTerms.TermIdentFromName(varContextName),
              IsaCommonTerms.TermIdentFromName("\\<Gamma>"),
              IsaCommonTerms.EmptyList);
            
            var lemmaManager = new AstToCfgLemmaManager(
                beforeCfgProgAccess,
                afterCfgProgAccess,
                astBoogieContext,
                cfgBoogieContext,
                afterCfg,
                funContextWfName,
                beforeDagOrigBlock,
                beforeToAfter,
                beforeCfgData,
                varFactory);

            var lemmaNamer = new IsaUniqueNamer();
            IList<OuterDecl> outerDecls = new List<OuterDecl>();

            outerDecls.Add(varContextAbbrev);
            outerDecls.Add(new DeclareDecl("Nat.One_nat_def[simp del]"));

            foreach (BigBlock beforeBlock in beforeCfgAst.GetBlocksBackwards())
            {
              Block afterBlock = beforeToAfter[beforeBlock];
              
              int bigblockIndex = proofGenInfo.GetMappingCopyBigBlockToIndex()[beforeBlock];

              BigBlock successorBigBlockOrig;
              BigBlock successorBigBlockCopy;
              int succBigBlockIndex = -1;
              Block successorBlock;
              int succBlockIndex = -1;
              if (proofGenInfo.GetMappingCopyBigblockToOrigBigblock()[beforeBlock].successorBigBlock != null)
              {
                successorBigBlockOrig = proofGenInfo.GetMappingCopyBigblockToOrigBigblock()[beforeBlock].successorBigBlock;
                successorBigBlockCopy = proofGenInfo.GetMappingOrigBigblockToCopyBigblock()[successorBigBlockOrig];
                succBigBlockIndex = proofGenInfo.GetMappingCopyBigBlockToIndex()[successorBigBlockCopy];
                successorBlock = beforeToAfter[successorBigBlockCopy];
                succBlockIndex = afterCfg.GetUniqueIntLabel(successorBlock);
              }

              (Block, Expr, BranchIndicator) hints = mappingWithHints[beforeBlock];

              if (beforeBlock.simpleCmds.Any() && multiCmdIsaVisitor.Translate(beforeBlock.simpleCmds).Any())
              {
                LemmaDecl localLemmaDecl = lemmaManager.LocalLemma(
                  beforeBlock,
                  afterBlock,
                  hints.Item2,
                  bigblock => GetLemmaName(bigblock, lemmaNamer, beforeCfgProgAccess.BigBlockInfo()),
                  hints.Item3
                );
                outerDecls.Add(localLemmaDecl);
              }
              
              LemmaDecl globalLemmaDecl =
                lemmaManager.GenerateGlobalLemma(
                  beforeBlock,
                  IsaCommonTerms.TermIdentFromName("cont_" + bigblockIndex),
                  afterBlock,
                  IsaCommonTerms.TermIdentFromName(beforeCfgProgAccess.BigBlockInfo().TheoryName + ".post"),
                  (hints.Item2, hints.Item3),
                  bigblock => GetGlobalLemmaName(bigblock, lemmaNamer, beforeCfgProgAccess.BigBlockInfo()),
                  proofGenInfo
                );
              outerDecls.Add(globalLemmaDecl);

              if (proofGenInfo.GetMappingCopyBigBlockToIndex()[beforeBlock] == 0)
              {
                entryLemma = globalLemmaDecl;
              }
            }

            var absValType = new VarType("a");
            var cfgToDagLemmasLocale = new LocaleDecl(
              "ast_to_cfg_lemmas",
              new ContextElem(
                new List<Tuple<TermIdent, TypeIsa>>
                {
                  Tuple.Create((TermIdent) astBoogieContext.absValTyMap,
                    IsaBoogieType.AbstractValueTyFunType(absValType)),
                  Tuple.Create((TermIdent) astBoogieContext.funContext, IsaBoogieType.FunInterpType(absValType))
                },
                new List<Term>
                {
                  IsaBoogieTerm.FunInterpWf(astBoogieContext.absValTyMap, beforeCfgProgAccess.FunctionsDecl(),
                    astBoogieContext.funContext)
                },
                new List<string> {funContextWfName}
              ),
              outerDecls
            );
            
            var theoryOuterDecls = new List<OuterDecl>();
            theoryOuterDecls.Add(cfgToDagLemmasLocale);

            if (generateEndtoEnd && !proofGenInfo.GetOptimizationsFlag())
            {
              var endToEndManager = new AstToCfgEndToEnd();
              var endToEndDecls = endToEndManager.EndToEndProof(
                entryLemma.Name,
                phasesTheories.EndToEndLemmaName(PhasesTheories.Phase.CfgToDag, false) + "_theorem_aux",
                vcAssm,
                beforeCfgProgAccess,
                afterCfgProgAccess,
                beforeCfgAst,
                proofGenInfo
              );
              theoryOuterDecls.AddRange(endToEndDecls);
            }

            List<string> importTheories = new List<string>
            {
              "Boogie_Lang.Ast", "Boogie_Lang.Ast_Cfg_Transformation", "Boogie_Lang.Semantics", "Boogie_Lang.Util",
              "Boogie_Lang.BackedgeElim", "Boogie_Lang.TypingML",
              beforeCfgProgAccess.TheoryName(),
              afterCfgProgAccess.TheoryName()
            };
            
            if (config.GenerateCfgDagProof) importTheories.Add(phasesTheories.TheoryName(PhasesTheories.Phase.CfgToDag));
            if (config.GeneratePassifProof) importTheories.Add(phasesTheories.TheoryName(PhasesTheories.Phase.Passification));
            if (config.GenerateVcProof) importTheories.Add(phasesTheories.TheoryName(PhasesTheories.Phase.Vc));

            return new Theory(
              uniqueTheoryName,
              importTheories,
              theoryOuterDecls
            );
        }

        public static bool PredHasLoop(BigBlock b, ASTRepr ast, out BigBlock predecessor)
        {
          IEnumerable<BigBlock> bbs = ast.GetBlocksForwards();
          BigBlock[] bbsArray = bbs.ToArray();

          for (var i = 0; i < bbsArray.Length; i++)
          {
            if (bbsArray[i] == b && i != 0 && bbsArray[i - 1].ec is WhileCmd)
            {
              predecessor = bbsArray[i - 1];
              return true;
            }
          }

          predecessor = null;
          return false;
        }

        private static string GetLemmaName(BigBlock b, IsaUniqueNamer namer, IsaBigBlockInfo bbInfo)
        {
            return namer.GetName(b, "rel_" + bbInfo.CmdsQualifiedName(b).First());
        }

        private static string GetGlobalLemmaName(BigBlock b, IsaUniqueNamer namer, IsaBigBlockInfo bbInfo)
        {
            return "global_" + namer.GetName(b, "rel_" + bbInfo.CmdsQualifiedName(b).First());
        }
    }
}