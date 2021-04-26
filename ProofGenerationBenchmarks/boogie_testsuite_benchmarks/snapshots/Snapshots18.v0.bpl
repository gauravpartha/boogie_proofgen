procedure  M();

implementation   M()
{
    while (true)
    {
        assert 0 == 0;
        
        call N();
        call N();

        if (*)
        {
            break;
        }

        assert 1 != 1;
    }

    assert 2 != 2;
}

procedure  N();
  ensures false;
