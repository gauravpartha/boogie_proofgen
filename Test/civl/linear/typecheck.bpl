// RUN: %boogie -useArrayTheory  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type X;

function {:inline} none() : [int]bool { (lambda i:int :: false) }
function {:inline} {:linear "A"} A_X_Collector(a: X) : [int]bool { none() }
function {:inline} {:linear "A"} A_int_Collector(a: int) : [int]bool { none() }
function {:inline} {:linear "B"} B_X_Collector(a: X) : [int]bool { none() }
function {:inline} {:linear "B"} B_XSet_Collector(a: [X]bool) : [int]bool { none() }
function {:inline} {:linear "C"} C_X_Collector(a: X) : [int]bool { none() }
function {:inline} {:linear "C"} C_XMulSet_Collector(a: [X]int) : [int]bool { none() }
function {:inline} {:linear "D"} D_X_Collector(a: X) : [int]bool { none() }
function {:inline} {:linear "D"} D_XSet_Collector(a: [X]bool) : [int]bool { none() }
function {:inline} {:linear "D2"} A2_X_Collector(a: X) : [int]bool { none() }
function {:inline} {:linear "x"} x_int_Collector(a: int) : [int]bool { none() }
function {:inline} {:linear ""} empty_int_Collector(a: int) : [int]bool { none() }

procedure A()
{
    var {:linear "A"} a: X;
    var {:linear "A"} b: int;
}

procedure B()
{
    var {:linear "B"} a: X;
    var {:linear "B"} b: [X]bool;
}

procedure C()
{
    var {:linear "C"} a: X;
    var {:linear "C"} c: [X]int;
}

function f(X): X;

procedure {:yields} {:layer 1} D()
{
    var {:linear "D"} a: X;
    var {:linear "D"} x: X;
    var {:linear "D"} b: [X]bool;
    var c: X;
    var {:linear "D2"} d: X;

    b[a] := true;

    a := f(a);

    a := c;

    c := a;

    a := d;

    a := a;

    a, x := x, a;

    a, x := x, x;

    call a, x := E(a, x);

    call a, x := E(a, a);

    call a, x := E(a, f(a));

    call a, x := E(a, d);

    call d, x := E(a, x);

    call a, x := E(c, x);

    call c, x := E(a, x);

    yield;
    par c := F(a) | x := F(a);
    yield;
}

procedure {:yields} {:layer 1} E({:linear_in "D"} a: X, {:linear_in "D"} b: X) returns ({:linear "D"} c: X, {:linear "D"} d: X)
{
    yield;
    c := a;
    yield;
}

procedure {:yields} {:layer 1} F({:linear_in "D"} a: X) returns ({:linear "D"} c: X);

var {:linear "x"} g:int;

procedure G(i:int) returns({:linear "x"} r:int)
{
  r := g;
}

procedure H(i:int) returns({:linear "x"} r:int)
modifies g;
{
  g := r;
}

procedure {:yields} {:layer 1} I({:linear_in ""} x:int) returns({:linear ""} x':int)
{
  yield;
  x' := x;
  yield;
}

procedure {:yields} {:layer 1} J()
{
  yield;
}

procedure {:yields} {:layer 1} P1({:linear_in ""} x:int) returns({:linear ""} x':int)
{
  yield;
  par x' := I(x) | J();
  yield;
  call x' := I(x');
  yield;
}

procedure {:yields} {:layer 1} P2({:linear_in ""} x:int) returns({:linear ""} x':int)
{
  yield;
  call x' := I(x);
  yield;
  par x' := I(x') | J();
  yield;
}

procedure {:yields} {:layer 1}
P({:linear "lin"} x: int, {:linear_in "lin"} y: int)
{
  par Q(x) | linear_yield_x(y) | linear_yield_x(y);
  par Q(x) | linear_yield_x(x) | linear_yield_x(y);
}

procedure {:yields} {:layer 1}
Q({:linear "lin"} a: int);

var {:layer 0,1} x:int;

procedure {:yield_invariant} {:layer 1} linear_yield_x({:linear "lin"} n: int);
requires x >= n;

function {:builtin "MapConst"} MapConstBool(bool) : [int]bool;
function {:inline} {:linear "lin"} TidCollector(x: int) : [int]bool
{
  MapConstBool(false)[x := true]
}
