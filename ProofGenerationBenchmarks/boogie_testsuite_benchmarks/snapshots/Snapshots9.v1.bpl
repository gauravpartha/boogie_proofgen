procedure  M(n: int);
  requires 0 < n;

implementation   M(n: int)
{
    var x: int;

    call x := N(n);

    assert 0 <= x;
}

procedure  N(n: int) returns (r: int);
  requires 0 < n;
  // Change: weaker postcondition
  ensures 0 <= r;
