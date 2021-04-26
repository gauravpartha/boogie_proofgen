var x: int;
var y: int;
var z: int;

procedure  M();
  modifies x, y, z;

implementation   M()
{
    z := 0;

    call N();

    assert y < 0;
}

procedure  N();
  // Change: fewer modified variables
  modifies x;
  ensures y < z;
