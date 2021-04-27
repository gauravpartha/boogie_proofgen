// elements in a[left..right] are partitioned at index according to value pivot
function is_LT_pivot (pivot: int, a: [int]int, left: int, right: int, index: int) returns(bool)
{ ( forall k: int  ::  left <= right  &&  left <= k  &&  k < index  ==>  a[k] <= pivot ) }

function is_GT_pivot (pivot: int, a: [int]int, left: int, right: int, index: int) returns(bool)
{ ( forall k: int  ::  left <= right  &&  index <= k  &&  k <= right  ==>  pivot <= a[k] ) }
// this should be derivable from the definition but it is needed nonetheless
axiom ( forall pivot: int, a: [int]int, left: int, right: int, index: int ::
		left <= right && is_GT_pivot(pivot, a, left, right-1, index) && pivot <= a[right]
			==> is_GT_pivot(pivot, a, left, right, index) );
// this should be derivable from the definition but it is needed nonetheless
axiom ( forall pivot: int, a: [int]int, left: int, right: int, index: int ::
		is_GT_pivot(pivot, a, left, right, index)	==> pivot <= a[index] );
			

					
procedure swap (a1: [int]int, i1 : int, j1: int) returns(b1: [int]int)
	// elements in positions i,j are swapped
	ensures (b1[i1] == a1[j1]  &&  b1[j1] == a1[i1]);
	// all other elements are unchanged
	ensures (forall k: int :: k != i1 && k != j1  ==>  b1[k] == a1[k]);
{
	var tmp: int;
	
	b1 := a1;
	tmp := b1[i1];
	b1[i1] := b1[j1];
	b1[j1] := tmp;
}


procedure partition (a: [int]int, left, right: int, pivot: int) returns(index: int, b: [int]int)
	requires left <= right;
	ensures is_LT_pivot(pivot, b, left, right, index);
	ensures is_GT_pivot(pivot, b, left, right, index);	
{
	var i: int;

	b := a;	
	i := left; index := left;
	while ( i <= right )
	invariant ( is_LT_pivot(pivot, b, left, i-1, index) );
	invariant ( is_GT_pivot(pivot, b, left, i-1, index) );
	invariant ( index <= i );	
	{
		if ( b[i] <= pivot )
		{
			call b := swap(b, i, index);
			index := index + 1;
		}
		i := i + 1;
	}
}
