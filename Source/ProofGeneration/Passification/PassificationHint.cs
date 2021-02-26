using Microsoft.Boogie;

namespace ProofGeneration.Passification
{
    public class PassificationHint
    {
        public PassificationHint(Cmd cmd, Variable origVar, Expr passiveExpr)
        {
            Cmd = cmd;
            OrigVar = origVar;
            PassiveExpr = passiveExpr;
        }

        public Variable OrigVar { get; }
        public Expr PassiveExpr { get; }
        public Cmd Cmd { get; }
    }
}