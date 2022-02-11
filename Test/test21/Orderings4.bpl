// RUN: %parallel-boogie -typeEncoding:p -logPrefix:0p "%s" > "%t"
// RUN: %diff "%s.p.expect" "%t"
// RUN: %parallel-boogie -typeEncoding:a -logPrefix:0a "%s" > "%t"
// RUN: %diff "%s.a.expect" "%t"


type Wicket;

const unique r: Wicket;
const unique s, t: Wicket extends unique r;

procedure P() returns () {
  assert (forall x:Wicket, y:Wicket :: x <: s && y <: t ==> x != y);
  assert false;          // unprovable
}
