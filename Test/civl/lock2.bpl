// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var {:layer 0,2} b: int;

procedure {:yields} {:layer 2} main()
{
    while (*)
    invariant {:cooperates} {:layer 1,2} true;
    {
        async call Customer();
    }
}

procedure {:yields} {:layer 2} Customer()
{
    while (*)
    invariant {:yields} {:layer 1,2} true;
    {
        call Enter();
        yield;
        call Leave();
    }
}

procedure {:atomic} {:layer 2} AtomicEnter()
modifies b;
{ assume b == 0; b := 1; }

procedure {:yields} {:layer 1} {:refines "AtomicEnter"} Enter()
{
    var _old, curr: int;

    while (true)
    invariant {:yields} {:layer 1} true;
    {
        call _old := CAS(0, 1);
        if (_old == 0) {
            break;
        }
        while (true)
        invariant {:yields} {:layer 1} true;
        {
            call curr := Read();
            if (curr == 0) {
                break;
            }
        }
    }
}

procedure {:atomic} {:layer 1,2} AtomicRead() returns (val: int)
{ val := b; }

procedure {:yields} {:layer 0} {:refines "AtomicRead"} Read() returns (val: int);

procedure {:atomic} {:layer 1,2} AtomicCAS(prev: int, next: int) returns (_old: int)
modifies b;
{
  _old := b;
  if (_old == prev) {
    b := next;
  }
}

procedure {:yields} {:layer 0} {:refines "AtomicCAS"} CAS(prev: int, next: int) returns (_old: int);

procedure {:atomic} {:layer 1,2} AtomicLeave()
modifies b;
{ b := 0; }

procedure {:yields} {:layer 0} {:refines "AtomicLeave"} Leave();
