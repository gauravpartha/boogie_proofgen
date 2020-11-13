﻿using System.Collections.Generic;
using Microsoft.Boogie.VCExprAST;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.Isa;
using ProofGeneration.VCProofGen;

namespace ProofGeneration.ProgramToVCProof
{
    public class TypeExtractorTranslator : IVCExprVisitor<Term, bool>
    {
        private readonly ConcreteTypeDeclTranslation typeTranslation;
        private readonly IDictionary<VCExprVar, Term> varToTerm;

        public TypeExtractorTranslator(BoogieContextIsa boogieContext, IDictionary<VCExprVar, Term> varToTerm)
        {
            typeTranslation = new ConcreteTypeDeclTranslation(boogieContext);
            this.varToTerm = varToTerm;
        }

        public Term TranslateExtractor(VCExpr extractor)
        {
            return extractor.Accept(this, true);
        }
        
        public Term Visit(VCExprLiteral node, bool arg)
        {
            throw new ProofGenUnexpectedStateException(GetType(), "only expect variables and function operations in extractors");
        }

        public Term Visit(VCExprNAry node, bool arg)
        {
            if (node.Op is VCExprBoogieFunctionOp vcFunOp)
            {
                if (typeTranslation.TryTranslateTypeDecl(vcFunOp.Func, out Term isaFun))
                {
                    List<Term> isaArgs = new List<Term>();
                    foreach(var nodeArg in node)
                    {
                        isaArgs.Add(nodeArg.Accept(this, arg));
                    }

                    return new TermApp(isaFun, isaArgs);
                }
                else
                {
                    throw new ProofGenUnexpectedStateException(GetType(), "unknown function operation in extractor");
                }
            }

            throw new ProofGenUnexpectedStateException(GetType(), "only expect variables and function operations in extractors");
        }

        public Term Visit(VCExprVar node, bool arg)
        {
            if (varToTerm.TryGetValue(node, out Term res))
            {
                return res;
            }
            else
            {
                throw new ProofGenUnexpectedStateException(GetType(), "unknown variable in extractor");
            }
        }

        public Term Visit(VCExprQuantifier node, bool arg)
        {
            throw new ProofGenUnexpectedStateException(GetType(), "only expect variables and function operations in extractors");
        }

        public Term Visit(VCExprLet node, bool arg)
        {
            throw new ProofGenUnexpectedStateException(GetType(), "only expect variables and function operations in extractors");
        }
    }
}