procedure p() {
    var y: int;
    var i: int;
    i := 0;
    y := 0;

    while ( i <= 10 ){
      y := y + i;
      i := i + 1;
    }

    assert y >= 0;
}