procedure  M();

implementation   M()
{
    assert true;

    call N();

    assert true;

    call N();

    assert false;
}

procedure  N();
  ensures false;
