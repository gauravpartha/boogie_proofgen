function dummy<T>(x: T) : T; //to force Boogie not to monomorphize
type IntArray;
function lookup(a: IntArray, idx: int) : int;

function is_max (m: int, a: IntArray, low: int, high: int) returns(bool);
axiom (forall m:int, a: IntArray, low:int, high:int ::
	       is_max(m,a,low,high) <==> ( forall j: int :: low <= j  && j <= high  ==>  lookup(a,j) <= m ));		
procedure max (a: IntArray, n: int) returns(m: int)
	requires n >= 0;
	ensures is_max(m, a, 1, n);
{
	var i: int;
	i := 1;  m := lookup(a,1);
	while ( i <= n )
	invariant ( 1 <= i  &&  i <= n + 1 );
	invariant ( is_max(m, a, 1, i - 1) );
	{
		if ( m <= lookup(a,i) )
		{ m := lookup(a,i); }
		i := i + 1;
	}
}