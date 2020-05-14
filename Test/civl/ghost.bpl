// RUN: %boogie -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var {:layer 0,2} x: int;

procedure {:right} {:layer 1} AtomicIncr()
modifies x;
{ x := x + 1; }

procedure {:yields} {:layer 0} {:refines "AtomicIncr"} Incr();

procedure {:intro} {:layer 1} ghost(y: int) returns (z: int)
{
  z := y + 1;
}

procedure {:right} {:layer 2} AtomicIncr2()
modifies x;
{ x := x + 2; }

procedure {:yields} {:layer 1} {:refines "AtomicIncr2"} Incr2()
{
  var {:layer 1} a: int;

  yield;
  call a := ghost(1);
  assert {:layer 1} a == 2;
  par Incr() | Incr();
  yield;
}

procedure {:intro} {:layer 1} ghost'() returns (z: int)
{
  z := x;
}

procedure {:yields} {:layer 1} {:refines "AtomicIncr2"} Incr2'()
{
  var {:layer 1} a: int;
  var {:layer 1} b: int;

  yield;
  call a := ghost'();
  par Incr() | Incr();
  call b := ghost'();
  assert {:layer 1} b == a + 2;
  yield;
}
