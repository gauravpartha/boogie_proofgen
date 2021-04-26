// RUN: %boogie -inline:spec -print:- -env:0 -printInlined "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure  foo()
  modifies x;
{
  x := x + 1;
  call foo();
}

procedure  foo1()
  modifies x;
{
  x := x + 1;
  call foo2();
}

procedure  foo2()
  modifies x;
{
  x := x + 1;
  call foo3();
}

procedure  foo3()
  modifies x;
{
  x := x + 1;
  call foo1();
}

var x:int;

procedure  bar()
  modifies x;
{
  call foo();
  call foo1();
}

