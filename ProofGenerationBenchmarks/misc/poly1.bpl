type Foo _;
type Bar _;

function convert<A>(x: Foo A) : Bar A;
function isValid<A>(x: A) : bool;
function someFoo<A>(i: int) : Foo A;

axiom (forall <T> :: (forall r : Foo T :: isValid(r) <==> !isValid(convert(r))));

procedure iterate_poly() returns (y: Bar int)
    requires true;
    ensures isValid(y);
{
    var i: int;
    var tempFoo: Foo int;
    var tempBar: Bar int;

    i := 0;
    tempFoo := someFoo(0);
    tempBar := convert(tempFoo);

    while(!isValid(tempBar)) 
        invariant tempBar == convert(tempFoo);
    {
        i := i+1;
        tempFoo := someFoo(i);
        tempBar := convert(tempFoo);
    }

    //set result
    y := tempBar;

    //this assertion verifies due to the loop condition + invariant + axiom
    assert !isValid(tempFoo);
}