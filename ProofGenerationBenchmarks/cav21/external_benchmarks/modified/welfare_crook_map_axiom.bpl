function dummy<T>(x: T) : T; //to force Boogie not to monomorphize
type IntArray;
function lookup(a: IntArray, idx: int) : int;

var af: IntArray;
var ag: IntArray;
var ah: IntArray;
function is_crook (left: int, i: int, j: int, k: int, a: IntArray, b: IntArray, c: IntArray) returns (bool);
axiom(forall left: int, i: int, j:int, k: int, a: IntArray, b: IntArray, c: IntArray ::
   is_crook(left,i,j,k,a,b,c) <==>  i >= left  &&  j >= left  && k >= left  && lookup(a,i) == lookup(b,j)  &&  lookup(b,j) == lookup(c,k));
function has_crook (left: int, n1: int, n2: int, n3: int, a: IntArray, b: IntArray, c: IntArray) returns (bool);
axiom (forall left:int, n1:int, n2:int, n3:int, a: IntArray, b: IntArray, c:IntArray ::
	 has_crook(left, n1, n2, n3, a, b, c) <==> ( exists i, j, k: int :: i <= n1 && j <= n2 && k <= n3 && is_crook(left, i, j, k, a, b, c) ));
axiom ( forall left: int, n1: int, n2: int, n3: int, a: IntArray, b: IntArray, c: IntArray ::
		!has_crook (left, n1, n2, n3, a, b, c) && lookup(a,n1+1) != lookup(b,n2+1)  ==>  !has_crook (left, n1+1, n2, n3, a, b, c) );
axiom ( forall left: int, n1: int, n2: int, n3: int, a: IntArray, b: IntArray, c: IntArray ::
		!has_crook (left, n1, n2, n3, a, b, c) && lookup(b,n2+1) != lookup(c,n3+1)  ==>  !has_crook (left, n1, n2+1, n3, a, b, c) );
axiom ( forall left: int, n1: int, n2: int, n3: int, a: IntArray, b: IntArray, c: IntArray ::
		!has_crook (left, n1, n2, n3, a, b, c) && lookup(c,n3+1) != lookup(a,n1+1)  ==>  !has_crook (left, n1, n2, n3+1, a, b, c) );
function earliest_crook (left: int, i: int, j: int, k: int, a: IntArray, b: IntArray, c: IntArray) returns (bool);
axiom ( forall left: int, i: int, j: int, k: int, a: IntArray, b: IntArray, c: IntArray ::
			earliest_crook(left, i, j, k, a, b, c)  ==>  is_crook(left, i, j, k ,a, b, c) );
axiom ( forall left: int, i: int, j: int, k: int, a: IntArray, b: IntArray, c: IntArray ::
			earliest_crook(left, i, j, k, a, b, c) && lookup(a,i+1) < lookup(b,j+1)  ==>  earliest_crook(left, i+1, j, k, a, b, c) );
axiom ( forall left: int, i: int, j: int, k: int, a: IntArray, b: IntArray, c: IntArray ::
			earliest_crook(left, i, j, k, a, b, c) && lookup(b,j+1) < lookup(c,k+1)  ==>  earliest_crook(left, i, j+1, k, a, b, c) );
axiom ( forall left: int, i: int, j: int, k: int, a: IntArray, b: IntArray, c: IntArray ::
			earliest_crook(left, i, j, k, a, b, c) && lookup(c,k+1) < lookup(a,i+1)  ==>  earliest_crook(left, i, j, k+1, a, b, c) );
procedure find_crook (left: int)
	returns (p_f, p_g, p_h: int)
	ensures p_f+1 >= left && p_g+1 >= left && p_h+1 >= left;
	ensures has_crook(left, p_f, p_g, p_h, af, ag, ah)  ==>  earliest_crook(left, p_f, p_g, p_h, af, ag, ah);
{
	p_f := left-1;
	p_g := left-1;
	p_h := left-1;
	
	while ( lookup(af,p_f+1) != lookup(ag,p_g+1)  ||  lookup(ag,p_g+1) != lookup(ah,p_h+1) )
	invariant p_f+1 >= left && p_g+1 >= left && p_h+1 >= left;
	invariant has_crook(left, p_f, p_g, p_h, af, ag, ah)  ==>  earliest_crook(left, p_f, p_g, p_h, af, ag, ah);
	{
		if ( lookup(af,p_f+1) < lookup(ag,p_g+1) ) {
			p_f := p_f + 1;
		} else {
			if ( lookup(ag,p_g+1) < lookup(ah,p_h+1) ) {
				p_g := p_g + 1;
			} else { 
					 p_h := p_h + 1;
			}
		}
	}
}
