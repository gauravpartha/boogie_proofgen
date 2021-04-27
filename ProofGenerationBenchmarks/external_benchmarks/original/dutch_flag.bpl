const blue: int;
const white: int;
const red: int;

function is_flag_color ( col: int ) returns (bool)
{ col == blue  ||  col == white  ||  col == red }

function is_flag_color_array ( a: [int]int, low: int, high: int) returns (bool)
{ ( forall i: int :: low <= i && i <= high  ==>  is_flag_color(a[i]) ) }

function monochrome ( a: [int]int, low: int, high: int, col: int) returns (bool)
{ ( forall i: int :: low <= i && i <= high  ==>  a[i] == col ) }


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


procedure make_flag (a: [int]int, n: int)
	returns (rb: [int]int, b: int, r: int)
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

	rb := a;
	b, i, r := 1, 1, n+1;
	
	while ( i < r )
	invariant is_flag_color_array(rb, 1, n);	
	invariant ( 1 <= b  &&  b <= i  &&  i <= r && r <= n+1 );
	invariant ( monochrome(rb, 1, b-1, blue) );
	invariant ( monochrome(rb, b, i-1, white) );	
	invariant ( monochrome(rb, r, n, red) );
	{
		if (rb[i] == blue)
		{
			call rb := swap(rb, b, i);
			i := i + 1;
			b := b + 1;
		}
		else
		{
			if (rb[i] == white)
			{
				i := i + 1;
			}
			else
			{
				r := r - 1;
				call rb := swap(rb, r, i);
			}
		}
	}
}

