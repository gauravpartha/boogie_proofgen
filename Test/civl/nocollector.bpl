// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var {:linear "L"} x:int;

procedure{:yields}{:layer 1} P()
{
}
