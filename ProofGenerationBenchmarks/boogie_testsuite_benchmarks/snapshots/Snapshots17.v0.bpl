procedure  M();

implementation   M()
{
    var x: int;

    x := 0;
    while (*)
    {
        while (*)
        {
            assert true;

            call N();

            call N();

            x := x + 1;

            assert x == 1;
        }

        call N();

        assert false;
    }

    assert true;
}

procedure  N();
  ensures false;
