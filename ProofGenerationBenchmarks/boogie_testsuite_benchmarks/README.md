This folder contains tests taken from the Boogie test suite in the 
[commit](https://github.com/boogie-org/boogie/tree/b4be7f72e3c74cfa9257f385e2c59613b8ced898/Test) 
and were used for our artifact. We included all files in the test suite that can 
easily be desugared manually into our subset and that verify after removing all 
attributes. Note that comments in the files were taken directly from the test 
suite and they refer to the files where the attributes were not removed. As a
result, there may be comments that suggest the file should not verify even though
it does verify when one removes the attributes.

We manually rewrote the following files into our subset
  - Multi-assignment to single assignment (for example, `i,j := 0,0` to `i := 0; j := 0`): 
  `extractloops/detLoopExtractNested.bpl`, `textbook/TuringFactorial.bpl`
  - Rewrite if-then-else expression. Files: `inline/expansion4.bpl` 
    (as a result, we also had to rewrite a function definiton to an explicit axiom), 
    `stratifiedinline/bar4.bpl`, `textbook/DivMod.bpl`
  - Rewrite block expression (for example, `(var y := x; foo(y))` to `foo(x)`). 
    Files: `monomorphize/monomorphize0.bpl`
  - Rewrite problematic procedure names with apostrophes. 
    Files: `monomorphize/monomorphize0.bpl`
  - Rewrite procedure calls within loops.
    Files: `extractloops/detLoopExtract.bpl`, `lock/Lock.bpl`

We have added comments "MANUAL REWRITE" in the places where we manually rewrote
something.