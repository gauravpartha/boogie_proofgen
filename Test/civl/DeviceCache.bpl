// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type {:linear "tid"} X;

const nil: X;
var {:layer 0,1} ghostLock: X;
var {:layer 0,1} lock: X;
var {:layer 0,1} currsize: int;
var {:layer 0,1} newsize: int;
var {:layer 0,1}{:linear "tid"} unallocated:[X]bool;

function {:inline} Inv(ghostLock: X, currsize: int, newsize: int) : (bool)
{
    0 <= currsize && currsize <= newsize &&
    (ghostLock == nil <==> currsize == newsize)
}

procedure {:yield_invariant} {:layer 1} Yield();
requires Inv(ghostLock, currsize, newsize);

procedure {:yield_invariant} {:layer 1} YieldToReadCache({:linear "tid"} tid: X, old_currsize: int);
requires tid != nil && old_currsize <= currsize;

procedure {:yield_invariant} {:layer 1} YieldToWriteCache({:linear "tid"} tid: X, old_currsize: int, old_newsize: int);
requires tid != nil && ghostLock == tid && old_currsize == currsize && old_newsize == newsize;

procedure {:yields} {:layer 1} Allocate() returns ({:linear "tid"} xl: X)
ensures {:layer 1} xl != nil;
{
    call xl := AllocateLow();
}

procedure {:yields} {:layer 1} main({:linear_in "tid"} xls: [X]bool)
requires {:layer 1} xls == MapConst(true);
{
    var {:linear "tid"} tid: X;

    call Init(xls);
    while (*)
    invariant {:yields} {:layer 1} {:yield_loop "Yield"} true;
    {
        par tid := Allocate() | Yield();
        async call Thread(tid);
    }
}

procedure {:yields} {:layer 1}
{:yield_preserves "Yield"}
Thread({:linear "tid"} tid: X)
requires {:layer 1} tid != nil;
{
    var start, size: int;
    var bytesRead, i, tmp: int;

    havoc start, size;
    assume (0 <= start && 0 <= size);

    bytesRead := size;
    call acquire(tid);
    call i := ReadCurrsize(tid);
    call tmp := ReadNewsize(tid);
    if (start + size <= i) {
        call release(tid);
        goto COPY_TO_BUFFER;
    } else if (tmp > i) {
        bytesRead := if (start <= i) then (i - start) else 0;
        call release(tid);
        goto COPY_TO_BUFFER;
    } else {
        call WriteNewsize(tid, start + size);
        call release(tid);
        goto READ_DEVICE;
    }

READ_DEVICE:
    call WriteCache(tid, start + size);
    call acquire(tid);
    call tmp := ReadNewsize(tid);
    call WriteCurrsize(tid, tmp);
    call release(tid);

COPY_TO_BUFFER:
    call ReadCache(tid, start, bytesRead);
}

procedure {:yields} {:layer 1}
{:yield_preserves "Yield"}
{:yield_preserves "YieldToWriteCache", tid, old(currsize), old(newsize)}
WriteCache({:linear "tid"} tid: X, index: int)
{
    var j: int;

    call j := ReadCurrsize(tid);
    while (j < index)
    invariant {:yields} {:layer 1} {:yield_loop "Yield"} {:yield_loop "YieldToWriteCache", tid, old(currsize), old(newsize)} true;
    invariant {:layer 1} old(currsize) <= j;
    {
        call WriteCacheEntry(tid, j);
        j := j + 1;
    }
}

procedure {:yields} {:layer 1}
{:yield_preserves "Yield"}
{:yield_preserves "YieldToReadCache", tid, old(currsize)}
ReadCache({:linear "tid"} tid: X, start: int, bytesRead: int)
requires {:layer 1} 0 <= start && 0 <= bytesRead;
requires {:layer 1} (bytesRead == 0 || start + bytesRead <= currsize);
{
    var j: int;

    j := 0;
    while(j < bytesRead)
    invariant {:yields} {:layer 1} {:yield_loop "Yield"} {:yield_loop "YieldToReadCache", tid, old(currsize)} true;
    invariant {:layer 1} 0 <= j;
    invariant {:layer 1} bytesRead == 0 || start + bytesRead <= currsize;
    {
        call ReadCacheEntry(tid, start + j);
        j := j + 1;
    }
}

procedure {:atomic} {:layer 1} AtomicInit({:linear_in "tid"} xls:[X]bool)
modifies currsize, newsize, lock, ghostLock;
{ assert xls == MapConst(true); currsize := 0; newsize := 0; lock := nil; ghostLock := nil; }

procedure {:yields} {:layer 0} {:refines "AtomicInit"} Init({:linear_in "tid"} xls:[X]bool);

procedure {:right} {:layer 1} AtomicReadCurrsize({:linear "tid"} tid: X) returns (val: int)
{ assert tid != nil; assert lock == tid || ghostLock == tid; val := currsize; }

procedure {:yields} {:layer 0} {:refines "AtomicReadCurrsize"} ReadCurrsize({:linear "tid"} tid: X) returns (val: int);

procedure {:right} {:layer 1} AtomicReadNewsize({:linear "tid"} tid: X) returns (val: int)
{ assert tid != nil; assert lock == tid || ghostLock == tid; val := newsize; }

procedure {:yields} {:layer 0} {:refines "AtomicReadNewsize"} ReadNewsize({:linear "tid"} tid: X) returns (val: int);

procedure {:atomic} {:layer 1} AtomicWriteNewsize({:linear "tid"} tid: X, val: int)
modifies newsize, ghostLock;
{ assert tid != nil; assert lock == tid && ghostLock == nil; newsize := val; ghostLock := tid; }

procedure {:yields} {:layer 0} {:refines "AtomicWriteNewsize"} WriteNewsize({:linear "tid"} tid: X, val: int);

procedure {:atomic} {:layer 1} AtomicWriteCurrsize({:linear "tid"} tid: X, val: int)
modifies currsize, ghostLock;
{ assert tid != nil; assert lock == tid && ghostLock == tid; currsize := val; ghostLock := nil; }

procedure {:yields} {:layer 0} {:refines "AtomicWriteCurrsize"} WriteCurrsize({:linear "tid"} tid: X, val: int);

procedure {:atomic} {:layer 1} AtomicReadCacheEntry({:linear "tid"} tid: X, index: int)
{ assert 0 <= index && index < currsize; }

procedure {:yields} {:layer 0} {:refines "AtomicReadCacheEntry"} ReadCacheEntry({:linear "tid"} tid: X, index: int);

procedure {:right} {:layer 1} AtomicWriteCacheEntry({:linear "tid"} tid: X, index: int)
{ assert tid != nil; assert currsize <= index && ghostLock == tid; }

procedure {:yields} {:layer 0} {:refines "AtomicWriteCacheEntry"} WriteCacheEntry({:linear "tid"} tid: X, index: int);

procedure {:right} {:layer 1} atomic_acquire({:linear "tid"} tid: X)
modifies lock;
{ assert tid != nil; assume lock == nil; lock := tid; }

procedure {:yields} {:layer 0} {:refines "atomic_acquire"} acquire({:linear "tid"} tid: X);

procedure {:left} {:layer 1} atomic_release({:linear "tid"} tid: X)
modifies lock;
{ assert tid != nil; assert lock == tid; lock := nil; }

procedure {:yields} {:layer 0} {:refines "atomic_release"} release({:linear "tid"} tid: X);

procedure {:atomic} {:layer 1} AtomicAllocateLow() returns ({:linear "tid"} tid: X)
modifies unallocated;
{ assume tid != nil; assume unallocated[tid]; unallocated[tid] := false; }

procedure {:yields} {:layer 0} {:refines "AtomicAllocateLow"} AllocateLow() returns ({:linear "tid"} tid: X);
