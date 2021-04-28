var g: int;
const c: int;

function f(x: int) : int;

procedure old_expr(x: int) 
    modifies g;
{
    var y:int;
    g := g+1;

    //this is the same as "assume f(old(g)+c) == f(x)*y"
    assume old(f(g+c) == f(x)*y);

    assert f(g+c-1) == f(x)*y;
}