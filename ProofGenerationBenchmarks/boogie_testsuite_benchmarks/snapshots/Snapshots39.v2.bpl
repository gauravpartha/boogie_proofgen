procedure {:checksum "-1"} Callee();

implementation   Callee()
{
    var r: int;

    call r := Sum(42);
    assert r != 0;
    assert r == (42 * 43) div 2;
}

procedure  Sum(n: int) returns (r: int);
  requires 0 <= n;
  ensures r == (n * (n + 1)) div 2;
