This folder contains benchmarks with algorithmic examples that were taken from
various sources:
The `original` folder contains the examples in their original form and
the `modified` folder contains the examples
desugared into the current subset supported by proof generation (except 
the ones from the Boogie test suite).
1. [BLT test suite](https://github.com/emptylambda/BLT/blob/master/benchmarks/GroupA/):
`array_partitioning.bpl`, `dutch_flag.bpl`, `max_of_array_v1.bpl`, `plateau.bpl`,
`sum_of_array.bpl`
2. [1st Verified Software Competition](https://link.springer.com/chapter/10.1007/978-3-642-21437-0_14): `Boogie_Summax.bpl` (note that the invariant
is not strong enough here; we strengthened the invariant in the `modified` 
folder)
3. Boogie test suite: `TuringFactorial.bpl`, `Find.bpl`, and `DivMod.bpl`