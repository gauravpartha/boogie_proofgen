//:: ProofGen(IgnoreFile)
// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
function  Lit<T>(x: T) : T;
axiom Lit(true);

procedure test()
{
    assert Lit(true);
}
