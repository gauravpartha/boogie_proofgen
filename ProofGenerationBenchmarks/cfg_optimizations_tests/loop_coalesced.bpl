procedure p() {
    var y: int;
    var i: int;
    i := 0;
    y := 0;

    while ( i <= 10 ){
      y := y + i;
      goto l1;
      
      l1:
      i := i + 1;
    }

}