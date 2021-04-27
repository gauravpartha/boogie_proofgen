
https://www.rise4fun.com/Boogie/OEv


// Returns the sum and the maximum of elements of an integer array "a" of length "N"


/* Description: Given an N-element array of natural numbers,
write a program to compute the sum and the maximum of the
elements in the array.
Properties: Given that N >= 0 and a[i] >= 0 for 0 <= i < N,
prove the post-condition that sum <= N * max.
*/

procedure sum_max (a: [int] int, N: int) returns (sum: int, max: int)
	requires 0 < N;
	ensures sum <= N*max;
{
	var i: int;
	sum := 0;
	max := 0;
	i := 0;
	while (i < N)
		invariant sum <= i*max;
		invariant i <= N;
	{
		if (max < a[i]) {
			max := a[i];
		}
		sum := sum + a[i];
		i := i + 1;
	}
}
