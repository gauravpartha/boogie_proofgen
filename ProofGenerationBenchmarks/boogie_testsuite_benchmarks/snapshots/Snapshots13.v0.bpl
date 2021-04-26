procedure  M();

implementation   M()
{
    call N();

    assert false;
}

procedure  N();
  ensures F() && G();

function  F() : bool
{
    true
}

function  G() : bool
{
    false
}
