// RUN: %boogie -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure {:atomic} {:layer 1} AtomicX() { }

procedure {:yields} {:layer 0} {:refines "AtomicX"} X();

procedure {:yields} {:layer 0} Y();

procedure {:yields} {:layer 1} main() {
  yield;
  call X();
  while (*)
  {
    call Y();
  }
  yield;
  assert {:layer 1} true;
}
