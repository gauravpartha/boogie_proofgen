// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var {:layer 0,1} x:int;

procedure {:yields} {:layer 1} p()
requires {:layer 1} x >= 5;
ensures  {:layer 1} x >= 8;
{
  call Incr(1);
  yield;
  assert {:layer 1} x >= 6;
  call Incr(1);
  yield;
  assert {:layer 1} x >= 7;
  call Incr(1);
}

procedure {:yields} {:layer 1} q()
{
  call Incr(3);
}

procedure {:atomic} {:layer 1,1} AtomicIncr(val: int)
modifies x;
{
  x := x + val;
}

procedure {:yields} {:layer 0} {:refines "AtomicIncr"} Incr(val: int);
