var x: int;
var y: int;

procedure  M();
  modifies x, y;

implementation   M()
{
    y := 0;

    call N();

    assert y == 0;
}

procedure  N();
  modifies x;
