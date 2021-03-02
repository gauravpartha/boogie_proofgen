using System;

namespace Isabelle.Ast
{
    public class IsabelleException : Exception
    {
        public IsabelleException(string msg) : base(msg)
        {
        }
    }
}