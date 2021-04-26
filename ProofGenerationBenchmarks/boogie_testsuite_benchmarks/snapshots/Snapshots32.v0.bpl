var g: int;

procedure  P();
  requires g == 0;
  modifies g;

implementation   P()
{
    call Q();
    assert 0 < g;
}

procedure  Q();
  modifies g;
  ensures old(g) < g;
