// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:linear "tid"} Tid = int;

const unique DEFAULT: int;
const unique CREATED: int;
const unique PROCESSED: int;
const unique FINISHED: int;

var status:[int]int;

const n: int;
axiom 0 <= n;

procedure {:left} {:layer 1} AtomicCreateTask({:linear "tid"} tid: int)
modifies status;
{
    assert status[tid] == DEFAULT;
    status[tid] := CREATED;
}
procedure {:yields} {:layer 0} {:refines "AtomicCreateTask"} CreateTask({:linear "tid"} tid: int);

procedure {:left}  {:layer 1} AtomicProcessTask({:linear "tid"} tid: int)
modifies status;
{
    assert status[tid] == CREATED;
    status[tid] := PROCESSED;
}
procedure {:yields} {:layer 0} {:refines "AtomicProcessTask"} ProcessTask({:linear "tid"} tid: int);

procedure {:left}  {:layer 1} AtomicFinishTask({:linear "tid"} tid: int)
modifies status;
{
    assert status[tid] == PROCESSED;
    status[tid] := FINISHED;
}
procedure {:yields} {:layer 0} {:refines "AtomicFinishTask"} FinishTask({:linear "tid"} tid: int);

procedure {:intro} {:layer 1} StatusSnapshot() returns (snapshot: [int]int)
{
  snapshot := status;
}

procedure {:yields} {:layer 0} {:refines "AtomicAlloc"} Alloc(i: int, {:linear_in "tid"} tidq: [int]bool) returns ({:linear "tid"} id: int, {:linear "tid"} tidq':[int]bool);
procedure {:both} {:layer 1} AtomicAlloc(i: int, {:linear_in "tid"} tidq: [int]bool) returns ({:linear "tid"} id: int, {:linear "tid"} tidq':[int]bool)
{ assert tidq[i]; id := i; tidq' := tidq[i := false]; }

procedure {:atomic} {:layer 2} AtomicMain({:linear_in "tid"} tids: [int]bool)
modifies status;
{
    assert (forall i: int :: 0 <= i && i < n <==> tids[i]);
    assert (forall i: int :: 0 <= i && i < n ==> status[i] == DEFAULT);
    status := (lambda j: int :: if (0 <= j && j < n) then FINISHED else status[j]);
}

procedure {:yields} {:layer 1} {:refines "AtomicMain"} Main({:linear_in "tid"} tids: [int]bool) {
    var i: int;
    var {:layer 1} snapshot: [int]int;
    var {:linear "tid"} tids': [int]bool;
    var {:linear "tid"} tid: int;

    i := 0;
    tids' := tids;
    call snapshot := StatusSnapshot();
    while (i < n)
    invariant {:cooperates} {:layer 1} true;
    invariant {:layer 1} 0 <= i && i <= n;
    invariant {:layer 1} (forall j: int :: i <= j && j < n <==> tids'[j]);
    invariant {:layer 1} status == (lambda j: int :: if (0 <= j && j < i) then FINISHED else snapshot[j]);
    {
        call tid, tids' := Alloc(i, tids');
        async call {:sync} StartClient(tid);
        i := i + 1;
    }
}

procedure {:yields} {:left} {:layer 1} StartClient({:linear_in "tid"} tid: int)
modifies status;
requires {:layer 1} status[tid] == DEFAULT;
ensures {:layer 1} status == old(status)[tid := FINISHED];
{
    async call {:sync} GetTask(tid);
}

procedure {:yields} {:left} {:layer 1} GetTask({:linear_in "tid"} tid: int)
modifies status;
requires {:layer 1} status[tid] == DEFAULT;
ensures {:layer 1} status == old(status)[tid := FINISHED];
{
    call CreateTask(tid);
    async call {:sync} GetTaskCallback(tid);
}

procedure {:yields} {:left} {:layer 1} GetTaskCallback({:linear_in "tid"} tid: int)
modifies status;
requires {:layer 1} status[tid] == CREATED;
ensures {:layer 1} status == old(status)[tid := FINISHED];
{
    call ProcessTask(tid);
    async call {:sync} CollectTask(tid);
}

procedure {:yields} {:left} {:layer 1} CollectTask({:linear_in "tid"} tid: int)
modifies status;
requires {:layer 1} status[tid] == PROCESSED;
ensures {:layer 1} status == old(status)[tid := FINISHED];
{
    call FinishTask(tid);
}
