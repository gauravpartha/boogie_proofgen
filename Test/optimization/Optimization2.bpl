// RUN: %parallel-boogie /noVerify /printModel:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure test0(n: int)
{
    assume {:minimize true} true;
}

procedure test1(n: int)
{
    assume {:maximize true} true;
}
