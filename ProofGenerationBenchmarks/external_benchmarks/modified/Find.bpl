const K: int;
function f(int) returns (int);
axiom (exists k: int :: f(k) == K);
procedure Find(a: int, b: int) returns (k: int)
  requires a <= b;
  requires (forall j: int :: a < j && j < b ==> f(j) != K);
  ensures f(k) == K;
{
  goto A, B, C;  // nondeterministically choose one of these 3 goto targets
  A:
    assume f(a) == K;  // assume we get here only if 'f' maps 'a' to 'K'
    k := a;
    return;
  B:
    assume f(b) == K;  // assume we get here only if 'f' maps 'b' to 'K'
    k := b;
    return;
  C:
    assume f(a) != K && f(b) != K;  // neither of the two above
    call k := Find(a-1, b+1);
    return;
}
procedure Main() returns (k: int)
  ensures f(k) == K;
{
  call k := Find(0, 0);
}
