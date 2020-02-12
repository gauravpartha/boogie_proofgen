using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using Microsoft.Boogie;
using ProofGeneration.Isa;

namespace ProofGeneration
{
    class ApplicableIsaVisitor : IAppliableVisitor<Term>
    {
        private IList<Term> _args;

        public ApplicableIsaVisitor(IList<Term> args)
        {
            _args = args;
        }

        public Term Visit(UnaryOperator unaryOperator)
        {
            throw new NotImplementedException();
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

            return IsaBoogieTerm.FunCall(functionCall.FunctionName, _args);
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
