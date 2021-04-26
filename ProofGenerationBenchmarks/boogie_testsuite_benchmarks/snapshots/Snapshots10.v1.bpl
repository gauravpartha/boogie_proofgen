procedure  M(n: int);
  requires 0 < n;

implementation   M(n: int)
{
    var x: int;

    call x := N(n);

    call O();

    assert 0 <= x;
}

procedure  N(n: int) returns (r: int);
  requires 0 < n;
  // Change: stronger postcondition
  ensures 42 < r;

procedure  O();
  ensures true;
