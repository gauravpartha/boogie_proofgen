using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.BoogieIsaInterface.VariableTranslation;
using ProofGeneration.Isa;

namespace ProofGeneration
{
    class ApplicableIsaVisitor : IAppliableVisitor<Term>
    {
        private readonly TypeParamInstantiation _typeInst;
        private readonly IList<Term> _args;

        private readonly TypeIsaVisitor typeIsaVisitor;

        public ApplicableIsaVisitor(TypeParamInstantiation typeInst, 
            IList<Term> args, 
            IVariableTranslation<TypeVariable> typeVarTranslation)
        {
            _typeInst = typeInst;
            _args = args;
            typeIsaVisitor = new TypeIsaVisitor(typeVarTranslation);
        }

        public Term Visit(UnaryOperator unaryOperator)
        {
            if(_args.Count != 1)
            {
                throw new ExprArgException();
            }

            return IsaBoogieTerm.Unop(unaryOperator.Op, _args[0]);
        }

        public Term Visit(BinaryOperator binaryOperator)
        {
            if(_args.Count != 2)
            {
                throw new ExprArgException();
            }

            return IsaBoogieTerm.Binop(binaryOperator.Op, _args[0], _args[1]);
        }

        public Term Visit(FunctionCall functionCall)
        {
            if(_args.Count != functionCall.ArgumentCount)
            {
                throw new ExprArgException();
            }

            List<Term> typeInstIsa = new List<Term>();
            foreach(var typeVar in _typeInst.FormalTypeParams)
            {
                Term t = typeIsaVisitor.Translate(_typeInst[typeVar]);
                typeInstIsa.Add(t);
            }

            return IsaBoogieTerm.FunCall(functionCall.FunctionName, typeInstIsa, _args);
        }

        public Term Visit(MapSelect mapSelect)
        {
            throw new NotImplementedException();
        }

        public Term Visit(MapStore mapStore)
        {
            throw new NotImplementedException();
        }

        public Term Visit(TypeCoercion typeCoercion)
        {
            throw new NotImplementedException();
        }

        public Term Visit(ArithmeticCoercion arithCoercion)
        {
            throw new NotImplementedException();
        }

        public Term Visit(IfThenElse ifThenElse)
        {
            throw new NotImplementedException();
        }
    }

    class ExprArgException : Exception
    {

    }

}
