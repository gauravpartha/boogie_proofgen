procedure  M();

implementation   M()
{
    call N();

    assert false;
}

procedure  N();
  ensures F();

function  F() : bool
{
    false
}
