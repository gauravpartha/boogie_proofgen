// RUN: %parallel-boogie -noVerify -print:- -env:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type {:sourcefile "test.ssc"} T; 

function {:source "test.scc"} f(int) returns (int);

const {:description "The largest integer value"} unique MAXINT: int;

axiom {:naming "MyFavoriteAxiom"} (forall i: int :: {f(i)} f(i) == i+1);

var {:description "memory"} $Heap: [ref, name]any;

var {:sort_of_like_a_trigger (forall i: int :: true)} Bla: [ref, name]any;

procedure {:use_impl 1} foo(x : int) returns(n : int);

implementation {:id 1} foo(x : int) returns(n : int)
{
  block1: return;
}

implementation {:id 2} foo(x : int) returns(n : int)
{
  block1: return;
}

type ref, any, name;


// allow \" and other backslashes rather liberally:

procedure
  {:myAttribute
        "h\n\"ello\"",
        "again",
        "and\\" a\"gain\"",
        again}
P();

const again: int;
