/* Example that shows:
   1) loops using only gotos and labels
   2) nested loops, where the loops have different modified variable sets
   3) jumps out of loops
*/
procedure goto_nested_different_mods(n: int, k: int) returns ()
{
    var i: int;
    var j: int;
    var other: int;
    
    assume k >= 0;
    assume other > 0;
    i := k+1;
    goto loopHead;

    //loop head of outer loop
    loopHead:
        /* first two assertions form the loop invariant (Boogie takes all assertions 
         * up to the first statement that is not an assumption/assertion as the loop invariant) */
        assert i > 0;
        assert other > 0;
        other := other+1;
        
        //this goto is a non-deterministic branch: both paths are considered (demonically)
        goto loopBodyStart, afterLoop; 

    loopBodyStart:
        assume i < n;
        havoc j;
        assume j > 0;
        goto loopHeadNested;

    /**loop head of inner loop:
       the inner loop only modifies i and j, while the outer loop modifies 
       i,j, and other
    */
    loopHeadNested:
        /** the first two assertions form the loop invariant of the inner loop.*/
        assert i > 0;
        assert j > 0;
        goto loopBodyNestedStart, loopBodyEnd;

    loopBodyNestedStart:
        assume j < n;
        i := i+1;
        
        /* here one of three things can happen:
           1) we continue in the inner loop (goto loopBodyNestedEnd)
           2) we go to back to the beginning of the outer loop (goto loopHead)
           3) we go jump out of the inner and outer loop (goto finalBlock)
           */
        goto loopBodyNestedEnd, loopHead, finalBlock;

    loopBodyNestedEnd:
        i := i+j+1;
        j := j+1;
        
        goto loopHeadNested;

    loopBodyEnd:
        assume j >= n;
        i := i+k;
        goto loopHead;

    afterLoop:
        assume i >= n;
        goto finalBlock;

    finalBlock:
        assert other > 0;
        assert i+1 > 1;
}