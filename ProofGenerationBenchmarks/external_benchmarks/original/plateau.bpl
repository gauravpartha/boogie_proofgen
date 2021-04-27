function is_ordered (a: [int]int) returns (bool)
{ ( forall k: int :: a[k] <= a[k+1] ) }
			
function has_plateau (a: [int]int, low: int, high: int, len: int) returns (bool);
axiom ( forall a: [int]int, low: int, high: int ::  high >= low  ==>  has_plateau(a, low, high, 1) );
axiom ( forall a: [int]int, low: int, high: int, len: int ::
						is_ordered(a)  &&  has_plateau(a, low, high, len)  ==>  has_plateau(a, low, high+1, len) );
axiom ( forall a: [int]int, low: int, high: int, len: int ::
						is_ordered(a)  &&  has_plateau(a, low, high, len)  &&  a[high+1] == a[high+1-len+1]  ==>  has_plateau(a, low, high+1, len+1) );

						
function no_longer_plateau (a: [int]int, low: int, high: int, len: int) returns (bool);
axiom ( forall a: [int]int, low: int, high: int, len: int ::  high >= low  &&  len >= high - low + 1  ==>  no_longer_plateau(a, low, high, len) );
axiom ( forall a: [int]int, low: int, high: int, len: int ::
						is_ordered(a)  &&  no_longer_plateau(a, low, high, len)  &&  a[high+1] != a[high+1-len+1]  ==>  no_longer_plateau(a, low, high+1, len) );
axiom ( forall a: [int]int, low: int, high: int, len: int ::
						is_ordered(a)  &&  no_longer_plateau(a, low, high, len)  &&  a[high+1] == a[high+1-len+1]  ==>  no_longer_plateau(a, low, high+1, len+1) );

			
procedure longest_plateau (a: [int]int, n: int)
	returns (p: int)
	requires n > 0;
	requires is_ordered (a);
	ensures p >= 1;
	ensures has_plateau (a, 1, n, p);
	ensures no_longer_plateau (a, 1, n, p);
{
	var i: int;
	
	i, p := 2, 1;

	while ( i <= n )
	invariant 1 <= p;
	invariant 1 <= i && i <= n + 1;
	invariant has_plateau (a, 1, i-1, p);
	invariant no_longer_plateau (a, 1, i-1, p);
	{
		if ( a[i] != a[i-p+1] )
		{
			i := i + 1;
		}
		else
		{
			assert (a[i] == a[i-p+1]);
			i := i + 1;
			p := p + 1;
		}
	}
}
