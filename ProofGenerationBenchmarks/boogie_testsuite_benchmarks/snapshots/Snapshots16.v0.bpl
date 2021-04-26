function  PlusOne(n: int) : int
{
    n + 1
}

function  F(n: int) : int;

axiom (forall n: int :: { F(n) } F(n) == PlusOne(n));

procedure  M();

implementation   M()
{
    assert F(0) == 1;
}
