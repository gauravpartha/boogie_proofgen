type MyArray _;
function dummy<T>(x: T) : T; //to force Boogie not to monomorphize
function lookup(a: MyArray int, idx: int) : int;
procedure sum_max_no_map (a: MyArray int, N: int) returns (sum: int, max: int)
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
		invariant i >= 0;
	{
		if (max < lookup(a,i)) {
			max := lookup(a,i);
		}
		sum := sum + lookup(a,i);
		i := i + 1;
	}
}