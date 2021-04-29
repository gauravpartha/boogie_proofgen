// RUN: %boogie /monomorphize "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function  foo<T>(x: T): T {
    x
}

/* MANUAL REWRITE 
function  foo'<T>(x: T): T {
*/
function  foo2<T>(x: T): T {
    /** MANUAL REWRITE 
    (var y := x; foo(y))
    */
    foo(x)
}

function  bar1<T>(x: T): T {
    foo2(x)
}

function  bar2<T>(x: T): T {
    foo2(x)
}

procedure A(a: int) returns (a': int)
ensures a' == a;
{
    a' := foo(a);
    a' := foo2(a);
}

procedure B(a: int) returns (a': int)
ensures a' == a;
{
    a' := bar1(a);
    a' := bar2(a');
}

procedure C(a: int) returns (a':int)
ensures a' == a;
{
    a':= bar1(bar2(a));
}

procedure D(a: int) returns (a':int)
ensures a' == a;
{
    a' := a - 1;
    /** MANUAL REWRITE
    a':= bar1((var x := a'; bar2(a')) + 1);
    */
    a':= bar1(bar2(a') + 1);
}

type X;
/*MANUAL REWRITE
procedure A'(a: X) returns (a': X)
*/
procedure A2(a: X) returns (a': X)
ensures a' == a;
{
    a' := foo(a);
    a' := foo2(a);
}

/*MANUAL REWRITE
procedure B'(a: X) returns (a': X)
*/
procedure B2(a: X) returns (a': X)
ensures a' == a;
{
    a' := bar1(a);
    a' := bar2(a');
}

/* MANUAL REWRITE
procedure C'(a: X) returns (a': X)
*/
procedure C2(a: X) returns (a': X)
ensures a' == a;
{
    a':= bar1(bar2(a));
}
