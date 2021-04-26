// RUN: %boogie /printNecessaryAssumes "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure test0(n: int)
{
    assume  0 < n;
    assert 0 <= n;  // verified under s0
}

procedure test1(n: int)
{
    assume 0 < n;
    assume  n == 3;
    assert 0 <= n;  // verified under true
}

procedure test2(n: int)
{
    assume 0 < n;
    assume  n <= 42;
    assume  42 <= n;
    assert n == 42;  // verified under s2 and s3
}
