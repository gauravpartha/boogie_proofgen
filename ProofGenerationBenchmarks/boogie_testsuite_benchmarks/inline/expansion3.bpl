// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
function  foo3(x:int, y:bool) returns(bool)
 { foo3(x,y) }

axiom foo3(1,false);

procedure baz1()
  requires foo3(2,false);
{
  assume foo3(1,true);
}

