function dummy<T>(x: T) : T; //to force Boogie not to monomorphize
type IntMap;
function select(m: IntMap, idx: int):int;
function store(m: IntMap, idx: int, val: int):IntMap;
axiom ( forall m: IntMap, idx:int, val:int :: select(store(m,idx,val), idx) == val);
axiom (forall m: IntMap, idx1:int, idx2:int, val:int :: idx1 != idx2 ==> select(store(m,idx1,val), idx2) == select(m,idx2));
function is_LT_pivot (pivot: int, a: IntMap, left: int, right: int, index: int) returns(bool);
axiom (forall pivot:int, a: IntMap, left: int, right: int, index: int ::
	is_LT_pivot(pivot,a,left,right,index) == 
	( forall k: int  ::  left <= right  &&  left <= k  &&  k < index  ==>  select(a,k) <= pivot )
);
function is_GT_pivot (pivot: int, a: IntMap, left: int, right: int, index: int) returns(bool);
axiom (forall pivot:int, a: IntMap, left: int, right: int, index: int ::
	is_GT_pivot(pivot,a,left,right,index) <==>
  ( forall k: int  ::  left <= right  &&  index <= k  &&  k <= right  ==>  pivot <= select(a,k) )
);
axiom ( forall pivot: int, a: IntMap, left: int, right: int, index: int ::
		left <= right && is_GT_pivot(pivot, a, left, right-1, index) && pivot <= select(a,right)
			==> is_GT_pivot(pivot, a, left, right, index) );
axiom ( forall pivot: int, a: IntMap, left: int, right: int, index: int ::
		is_GT_pivot(pivot, a, left, right, index)	==> pivot <= select(a,index) );			
procedure swap (a1: IntMap, i1 : int, j1: int) returns(b1: IntMap)
	ensures (select(b1,i1) == select(a1,j1)  &&  select(b1,j1) == select(a1,i1));
	ensures (forall k: int :: k != i1 && k != j1  ==>  select(b1,k) == select(a1,k));
{
	var tmp: int;	
	b1 := a1;
	tmp := select(b1,i1);	
	b1 := store(b1, i1, select(b1,j1));	
	b1 := store(b1, j1, tmp);
}
procedure partition (a: IntMap, left, right: int, pivot: int) returns(index: int, b: IntMap)
	requires left <= right;
	ensures is_LT_pivot(pivot, b, left, right, index);
	ensures is_GT_pivot(pivot, b, left, right, index);	
{
	var i: int;
	var b_old: IntMap;

	b := a;	
	i := left; index := left;
	while ( i <= right )
	invariant ( is_LT_pivot(pivot, b, left, i-1, index) );
	invariant ( is_GT_pivot(pivot, b, left, i-1, index) );
	invariant ( index <= i );	
	{
		if ( select(b,i) <= pivot )
		{
			b_old := b;
			havoc b;
			assume (select(b,i) == select(b_old,index)  &&  select(b,index) == select(b_old,i));
			assume (forall k: int :: k != i && k != index  ==>  select(b,k) == select(b_old,k));
			index := index + 1;
		}
		i := i + 1;
	}
}