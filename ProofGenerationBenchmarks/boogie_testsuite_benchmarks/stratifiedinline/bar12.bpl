// RUN: %boogie -stratifiedInline:1 -vc:i "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
function  f(a:bool) : bool { true }

procedure  main()
{
  var x: int;
   assume f(x >= 0);
  assume x >= 0;
}
