function dummy<T>(x: T) : T; //to force Boogie not to monomorphize
type IntArray;
function lookup(a: IntArray, idx: int) : int;

function is_ordered (a: IntArray) returns (bool);
axiom (forall a: IntArray :: is_ordered(a) <==> ( forall k: int :: lookup(a,k) <= lookup(a,k+1) ));
			
function has_plateau (a: IntArray, low: int, high: int, len: int) returns (bool);
axiom ( forall a: IntArray, low: int, high: int ::  high >= low  ==>  has_plateau(a, low, high, 1) );
axiom ( forall a: IntArray, low: int, high: int, len: int ::
						is_ordered(a)  &&  has_plateau(a, low, high, len)  ==>  has_plateau(a, low, high+1, len) );
axiom ( forall a: IntArray, low: int, high: int, len: int ::
						is_ordered(a)  &&  has_plateau(a, low, high, len)  &&  lookup(a,high+1) == lookup(a,high+1-len+1)  ==>  has_plateau(a, low, high+1, len+1) );

						
function no_longer_plateau (a: IntArray, low: int, high: int, len: int) returns (bool);
axiom ( forall a: IntArray, low: int, high: int, len: int ::  high >= low  &&  len >= high - low + 1  ==>  no_longer_plateau(a, low, high, len) );
axiom ( forall a: IntArray, low: int, high: int, len: int ::
						is_ordered(a)  &&  no_longer_plateau(a, low, high, len)  &&  lookup(a,high+1) != lookup(a,high+1-len+1)  ==>  no_longer_plateau(a, low, high+1, len) );
axiom ( forall a: IntArray, low: int, high: int, len: int ::
						is_ordered(a)  &&  no_longer_plateau(a, low, high, len)  &&  lookup(a,high+1) == lookup(a,high+1-len+1)  ==>  no_longer_plateau(a, low, high+1, len+1) );

			
procedure longest_plateau (a: IntArray, n: int)
	returns (p: int)
	requires n > 0;
	requires is_ordered (a);
	ensures p >= 1;
	ensures has_plateau (a, 1, n, p);
	ensures no_longer_plateau (a, 1, n, p);
{
	var i: int;
	
	i := 2;
	p := 1;

	while ( i <= n )
	invariant 1 <= p;
	invariant 1 <= i && i <= n + 1;
	invariant has_plateau (a, 1, i-1, p);
	invariant no_longer_plateau (a, 1, i-1, p);
	{
		if ( lookup(a,i) != lookup(a,i-p+1) )
		{
			i := i + 1;
		}
		else
		{
			assert (lookup(a,i) == lookup(a,i-p+1));
			i := i + 1;
			p := p + 1;
		}
	}
}
