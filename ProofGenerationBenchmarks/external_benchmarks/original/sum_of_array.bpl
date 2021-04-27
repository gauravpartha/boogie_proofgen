// sum of content of a from position to position
function sum_from_to([int]int, int, int) returns(int);
axiom ( forall a: [int]int, low, high: int ::
				high < low   ==>  sum_from_to(a,low,high) == 0 );
axiom ( forall a: [int]int, low, high: int ::
				high >= low  ==>  sum_from_to(a,low,high-1) + a[high] == sum_from_to(a,low,high) );

procedure sum (a: [int]int, n: int) returns(s: int)
	requires n >= 0;
	ensures s == sum_from_to(a, 1, n);
{
	var i: int;
	i := 1;  s := 0;
	while ( i <= n )
	invariant ( 1 <= i  &&  i <=  n + 1);
	invariant ( s == sum_from_to(a, 1, i - 1) );
	{
		s := s + a[i];
		i := i + 1;
	}
}
