function dummy<T>(x: T) : T; //to force Boogie not to monomorphize
type IntMap;
function select(m: IntMap, idx: int):int;
function store(m: IntMap, idx: int, val: int):IntMap;
axiom (forall m: IntMap, idx:int, val:int :: select(store(m,idx,val), idx) == val);
axiom (forall m: IntMap, idx1:int, idx2:int, val:int :: idx1 != idx2 ==> select(store(m,idx1,val), idx2) == select(m,idx2));

const blue: int;
const white: int;
const red: int;

function is_flag_color ( col: int ) returns (bool);
axiom (forall col:int :: is_flag_color(col) <==> (col == blue  ||  col == white  ||  col == red));

function is_flag_color_array ( a: IntMap, low: int, high: int) returns (bool);
axiom (forall a: IntMap, low:int, high:int ::
	  is_flag_color_array(a,low,high) <==> ( forall i: int :: low <= i && i <= high  ==>  is_flag_color(select(a,i)) ));

function monochrome ( a: IntMap, low: int, high: int, col: int) returns (bool);
axiom (forall a: IntMap, low:int, high:int,col:int ::
	monochrome(a,low,high,col) <==> ( forall i: int :: low <= i && i <= high  ==>  select(a,i) == col ));

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
procedure make_flag (a: IntMap, n: int)
	returns (rb: IntMap, b: int, r: int)
	requires n >= 1;
	requires is_flag_color_array(a, 1, n);
	ensures 1 <= b;
	ensures b <= r;
	ensures r <= n+1;
	ensures monochrome(rb, 1, b-1, blue);
	ensures monochrome(rb, b, r-1, white);	
	ensures monochrome(rb, r, n, red);
{
	var i: int;
	var rb_old: IntMap;
	rb := a;
	b := 1; i := 1; r := n+1;
	while ( i < r )
	invariant is_flag_color_array(rb, 1, n);	
	invariant ( 1 <= b  &&  b <= i  &&  i <= r && r <= n+1 );
	invariant ( monochrome(rb, 1, b-1, blue) );
	invariant ( monochrome(rb, b, i-1, white) );	
	invariant ( monochrome(rb, r, n, red) );
	{
		if (select(rb,i) == blue)
		{
			rb_old := rb;
			havoc rb;
			assume (select(rb,b) == select(rb_old,i)  &&  select(rb,i) == select(rb_old,b));
			assume (forall k: int :: k != b && k != i  ==>  select(rb,k) == select(rb_old,k));
			
			i := i + 1;
			b := b + 1;
		}
		else
		{
			if (select(rb,i) == white)
			{
				i := i + 1;
			}
			else
			{
				r := r - 1;
				rb_old := rb;
				havoc rb;
				assume (select(rb,r) == select(rb_old,i)  &&  select(rb,i) == select(rb_old,r));
				assume (forall k: int :: k != r && k != i  ==>  select(rb,k) == select(rb_old,k));			
			}
		}
	}	
}

