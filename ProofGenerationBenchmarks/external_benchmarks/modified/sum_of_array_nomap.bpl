function dummy<T>(x: T) : T; //to force Boogie not to monomorphize
type IntArray;
function lookup(a: IntArray, idx: int) : int;

function sum_from_to(IntArray, int, int) returns(int);
axiom ( forall a: IntArray, low, high: int ::
				high < low   ==>  sum_from_to(a,low,high) == 0 );
axiom ( forall a: IntArray, low, high: int ::
				high >= low  ==>  sum_from_to(a,low,high-1) + lookup(a,high) == sum_from_to(a,low,high) );

procedure sum (a: IntArray, n: int) returns(s: int)
	requires n >= 0;
	ensures s == sum_from_to(a, 1, n);
{
	var i: int;
	i := 1;  s := 0;
	while ( i <= n )
	invariant ( 1 <= i  &&  i <=  n + 1);
	invariant ( s == sum_from_to(a, 1, i - 1) );
	{
		s := s + lookup(a,i);
		i := i + 1;
	}
}
