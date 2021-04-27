// sum of content of A from position to position
function is_max (m: int, a: [int]int, low: int, high: int) returns(bool)
{ ( forall j: int :: low <= j  && j <= high  ==>  a[j] <= m ) }
				
procedure max (a: [int]int, n: int) returns(m: int)
	requires n >= 0;
	ensures is_max(m, a, 1, n);
{
	var i: int;
	i := 1;  m := a[1];
	while ( i <= n )
	invariant ( 1 <= i  &&  i <= n + 1 );
	invariant ( is_max(m, a, 1, i - 1) );
	{
		if ( m <= a[i] )
		{ m := a[i]; }
		i := i + 1;
	}
}
