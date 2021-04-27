var af: [int]int;
var ag: [int]int;
var ah: [int]int;

function is_crook (left: int, i: int, j: int, k: int, a: [int]int, b: [int]int, c: [int]int) returns (bool)
{  i >= left  &&  j >= left  && k >= left  && a[i] == b[j]  &&  b[j] == c[k]  }

function has_crook (left: int, n1: int, n2: int, n3: int, a: [int]int, b: [int]int, c: [int]int) returns (bool)
{ ( exists i, j, k: int :: i <= n1 && j <= n2 && k <= n3 && is_crook(left, i, j, k, a, b, c) ) }
axiom ( forall left: int, n1: int, n2: int, n3: int, a: [int]int, b: [int]int, c: [int]int ::
		!has_crook (left, n1, n2, n3, a, b, c) && a[n1+1] != b[n2+1]  ==>  !has_crook (left, n1+1, n2, n3, a, b, c) );
axiom ( forall left: int, n1: int, n2: int, n3: int, a: [int]int, b: [int]int, c: [int]int ::
		!has_crook (left, n1, n2, n3, a, b, c) && b[n2+1] != c[n3+1]  ==>  !has_crook (left, n1, n2+1, n3, a, b, c) );
axiom ( forall left: int, n1: int, n2: int, n3: int, a: [int]int, b: [int]int, c: [int]int ::
		!has_crook (left, n1, n2, n3, a, b, c) && c[n3+1] != a[n1+1]  ==>  !has_crook (left, n1, n2, n3+1, a, b, c) );

function earliest_crook (left: int, i: int, j: int, k: int, a: [int]int, b: [int]int, c: [int]int) returns (bool);
axiom ( forall left: int, i: int, j: int, k: int, a: [int]int, b: [int]int, c: [int]int ::
			earliest_crook(left, i, j, k, a, b, c)  ==>  is_crook(left, i, j, k ,a, b, c) );
axiom ( forall left: int, i: int, j: int, k: int, a: [int]int, b: [int]int, c: [int]int, i2: int, j2: int, k2: int ::
			earliest_crook(left, i, j, k, a, b, c) && a[i+1] < b[j+1]  ==>  earliest_crook(left, i+1, j, k, a, b, c) );
axiom ( forall left: int, i: int, j: int, k: int, a: [int]int, b: [int]int, c: [int]int, i2: int, j2: int, k2: int ::
			earliest_crook(left, i, j, k, a, b, c) && b[j+1] < c[k+1]  ==>  earliest_crook(left, i, j+1, k, a, b, c) );
axiom ( forall left: int, i: int, j: int, k: int, a: [int]int, b: [int]int, c: [int]int, i2: int, j2: int, k2: int ::
			earliest_crook(left, i, j, k, a, b, c) && c[k+1] < a[i+1]  ==>  earliest_crook(left, i, j, k+1, a, b, c) );

					

procedure find_crook (left: int)
	returns (p_f, p_g, p_h: int)
	ensures p_f+1 >= left && p_g+1 >= left && p_h+1 >= left;
	ensures has_crook(left, p_f, p_g, p_h, af, ag, ah)  ==>  earliest_crook(left, p_f, p_g, p_h, af, ag, ah);
{
	p_f, p_g, p_h := left-1, left-1, left-1;
	
	while ( af[p_f+1] != ag[p_g+1]  ||  ag[p_g+1] != ah[p_h+1] )
	invariant p_f+1 >= left && p_g+1 >= left && p_h+1 >= left;
	invariant has_crook(left, p_f, p_g, p_h, af, ag, ah)  ==>  earliest_crook(left, p_f, p_g, p_h, af, ag, ah);
	{
		if ( af[p_f+1] < ag[p_g+1] ) {
			p_f := p_f + 1;
		} else {
			if ( ag[p_g+1] < ah[p_h+1] ) {
				p_g := p_g + 1;
			} else { 
					 // assert ( ah[p_h+1] < af[p_f+1] );
					 p_h := p_h + 1;
			}
		}
	}
}
