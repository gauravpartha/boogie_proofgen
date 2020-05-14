// RUN: %boogie -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

const n:int;
axiom n >= 1;

type val = int;
type pid = int;

function {:inline} pid(i:int) : bool { 1 <= i && i <= n }

type {:pending_async}{:datatype} PA;
function {:pending_async "BROADCAST"}{:constructor} BROADCAST_PA(i:pid) : PA;
function {:pending_async "COLLECT"}{:constructor} COLLECT_PA(i:pid) : PA;

function trigger(x:int) : bool { true }

function {:inline} NoPAs () : [PA]int
{ (lambda pa:PA :: 0) }

function {:inline} InitialPAs (k:pid) : [PA]int
{
  MapAddPA(
    (lambda pa:PA :: if is#BROADCAST_PA(pa) && pid(i#BROADCAST_PA(pa)) && i#BROADCAST_PA(pa) < k then 1 else 0),
    (lambda pa:PA :: if is#COLLECT_PA(pa) && pid(i#COLLECT_PA(pa)) && i#COLLECT_PA(pa) < k then 1 else 0)
  )
}

function {:inline} AllBroadcasts () : [PA]int
{ (lambda pa:PA :: if is#BROADCAST_PA(pa) && pid(i#BROADCAST_PA(pa)) then 1 else 0) }

function {:inline} AllCollects () : [PA]int
{ (lambda pa:PA :: if is#COLLECT_PA(pa) && pid(i#COLLECT_PA(pa)) then 1 else 0) }

function {:inline} RemainingBroadcasts (k:pid) : [PA]int
{ (lambda pa:PA :: if is#BROADCAST_PA(pa) && k < i#BROADCAST_PA(pa) && i#BROADCAST_PA(pa) <= n then 1 else 0) }

function {:inline} RemainingCollects (k:pid) : [PA]int
{ (lambda pa:PA :: if is#COLLECT_PA(pa) && k < i#COLLECT_PA(pa) && i#COLLECT_PA(pa) <= n then 1 else 0) }

////////////////////////////////////////////////////////////////////////////////

var {:layer 0,1} CH_low:[pid][val]int;
var {:layer 1,4} CH:[val]int;
var {:layer 0,4} value:[pid]val;
var {:layer 0,4} decision:[pid]val;

function max(CH:[val]int) : val;
function card(CH:[val]int) : int;

axiom card(MultisetEmpty) == 0;
axiom (forall CH:[val]int, v:val :: card(MultisetPlus(CH, MultisetSingleton(v))) == card(CH) + 1);
axiom (forall CH:[val]int, v:val :: {CH[v := CH[v] + 1]} card(CH[v := CH[v] + 1]) == card(CH) + 1);
axiom (forall m:[val]int, m':[val]int :: {card(m), card(m')} MultisetSubsetEq(m, m') && card(m) == card(m') ==> m == m');

axiom (forall v:val :: max(MultisetSingleton(v)) == v);
axiom (forall CH:[val]int, v:val :: { CH[v := CH[v] + 1] } max(CH[v := CH[v] + 1]) == (if v > max(CH) then v else max(CH)));

function value_card(v:val, value:[pid]val, i:pid, j:pid) : int
{
  if j < i then
    0
  else
    if value[j] == v then
      value_card(v, value, i, j-1) + 1
    else
      value_card(v, value, i, j-1)
}

////////////////////////////////////////////////////////////////////////////////

// NOTE: CIVL currently does not support variables to be liner in multiple
// domains (i.e., supplying multiple linear annotations). In the future we
// would like the MAIN action(s) to take a single parameter as follows:
//     {:linear_in "broadcast"}{:linear_in "collect"} pids:[pid]bool

procedure {:atomic}{:layer 4}
MAIN''({:linear_in "broadcast"} pidsBroadcast:[pid]bool, {:linear_in "collect"} pidsCollect:[pid]bool)
modifies CH, decision;
{
  assert pidsBroadcast == (lambda i:pid :: pid(i)) && pidsCollect == pidsBroadcast;
  assert CH == MultisetEmpty;
  CH := (lambda v:val :: value_card(v, value, 1, n));
  assume card(CH) == n;
  assume MultisetSubsetEq(MultisetEmpty, CH);
  // havoc decision;
  // assume (forall i:pid :: 1 <= i && i <= n ==> decision[i] == max(CH));
  decision := (lambda i:pid :: if pid(i) then max(CH) else old(decision)[i]);
}

procedure {:IS_invariant}{:layer 3}
INV_COLLECT_ELIM({:linear_in "broadcast"} pidsBroadcast:[pid]bool, {:linear_in "collect"} pidsCollect:[pid]bool)
returns ({:pending_async "COLLECT"} PAs:[PA]int, {:choice} choice:PA)
modifies CH, decision;
{
  assert pidsBroadcast == (lambda i:pid :: pid(i)) && pidsCollect == pidsBroadcast;
  assert CH == MultisetEmpty;

  CH := (lambda v:val :: value_card(v, value, 1, n));
  assume card(CH) == n;
  assume MultisetSubsetEq(MultisetEmpty, CH);

  havoc decision;

  assume
  (exists k:int :: {trigger(k)} 0 <= k && k <= n && trigger(k+1) &&
    // (forall i:pid :: 1 <= i && i <= k ==> decision[i] == max(CH)) &&
    decision == (lambda i:pid :: if 1 <= i && i <= k then max(CH) else old(decision)[i]) &&
    PAs == RemainingCollects(k) &&
    choice == COLLECT_PA(k+1) &&
    (k < n ==> PAs[COLLECT_PA(n)] > 0) // help for the prover
  );
}

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 3}
{:IS "MAIN''","INV_COLLECT_ELIM"}{:elim "COLLECT","COLLECT'"}
MAIN'({:linear_in "broadcast"} pidsBroadcast:[pid]bool, {:linear_in "collect"} pidsCollect:[pid]bool)
returns ({:pending_async "COLLECT"} PAs:[PA]int)
modifies CH;
{
  assert pidsBroadcast == (lambda i:pid :: pid(i)) && pidsCollect == pidsBroadcast;
  assert CH == MultisetEmpty;
  assert trigger(0);

  CH := (lambda v:val :: value_card(v, value, 1, n));
  assume card(CH) == n;
  assume MultisetSubsetEq(MultisetEmpty, CH);
  PAs := AllCollects();
}

procedure {:atomic}{:layer 2}
{:IS "MAIN'","INV_BROADCAST_ELIM"}{:elim "BROADCAST"}
MAIN({:linear_in "broadcast"} pidsBroadcast:[pid]bool, {:linear_in "collect"} pidsCollect:[pid]bool)
returns ({:pending_async "BROADCAST","COLLECT"} PAs:[PA]int)
{
  assert pidsBroadcast == (lambda i:pid :: pid(i)) && pidsCollect == pidsBroadcast;
  assert CH == MultisetEmpty;
  assert trigger(0);

  PAs := MapAddPA(AllBroadcasts(), AllCollects());
}

procedure {:IS_invariant}{:layer 2}
INV_BROADCAST_ELIM({:linear_in "broadcast"} pidsBroadcast:[pid]bool, {:linear_in "collect"} pidsCollect:[pid]bool)
returns ({:pending_async "BROADCAST","COLLECT"} PAs:[PA]int, {:choice} choice:PA)
modifies CH;
{
  assert pidsBroadcast == (lambda i:pid :: pid(i)) && pidsCollect == pidsBroadcast;
  assert CH == MultisetEmpty;

  havoc CH;

  assume
  (exists k:int :: {trigger(k)} 0 <= k && k <= n && trigger(k+1) &&
    CH == (lambda v:val :: value_card(v, value, 1, k)) &&
    card(CH) == k &&
    MultisetSubsetEq(MultisetEmpty, CH) &&
    PAs == MapAddPA(RemainingBroadcasts(k), AllCollects()) &&
    choice == BROADCAST_PA(k+1) &&
    (k < n ==> PAs[BROADCAST_PA(n)] > 0) // help for the prover
  );
}

procedure {:left}{:layer 2} BROADCAST({:linear_in "broadcast"} i:pid)
modifies CH;
{
  assert pid(i);
  CH := CH[value[i] := CH[value[i]] + 1];
}

procedure {:atomic}{:layer 2,3} COLLECT({:linear_in "collect"} i:pid)
modifies decision;
{
  var received_values:[val]int;
  assert pid(i);
  assume card(received_values) == n;
  assume MultisetSubsetEq(MultisetEmpty, received_values);
  assume MultisetSubsetEq(received_values, CH);
  decision[i] := max(received_values);
}

procedure {:IS_abstraction}{:layer 3} COLLECT'({:linear_in "collect"} i:pid)
modifies decision;
{
  assert pid(i);
  assert CH == (lambda v:val :: value_card(v, value, 1, n));
  assert card(CH) == n;
  assert MultisetSubsetEq(MultisetEmpty, CH);
  decision[i] := max(CH);
}

////////////////////////////////////////////////////////////////////////////////

function Inv(CH_low:[pid][val]int, CH:[val]int) : bool
{
  (forall i:pid :: MultisetSubsetEq(MultisetEmpty, CH_low[i]) && MultisetSubsetEq(CH_low[i], CH))
}

procedure {:intro}{:layer 1} intro (i:pid)
modifies CH;
{
  CH := CH[value[i] := CH[value[i]] + 1];
}

////////////////////////////////////////////////////////////////////////////////

procedure {:intro}{:layer 1} Snapshot() returns (snapshot:[pid][val]int)
{
  snapshot := CH_low;
}

procedure {:yields}{:layer 1}{:refines "MAIN"}
Main({:linear_in "broadcast"} pidsBroadcast:[pid]bool, {:linear_in "collect"} pidsCollect:[pid]bool)
requires {:layer 1} pidsBroadcast == (lambda ii:pid :: pid(ii)) && pidsCollect == pidsBroadcast;
requires {:layer 1} (forall ii:pid :: CH_low[ii] == MultisetEmpty);
requires {:layer 1} CH == MultisetEmpty;
{
  var {:pending_async}{:layer 1} PAs:[PA]int;
  var i:pid;
  var {:linear "broadcast"} s:pid;
  var {:linear "collect"} r:pid;
  var {:linear "broadcast"} ss:[pid]bool;
  var {:linear "collect"} rr:[pid]bool;
  yield;
  assert {:layer 1} pidsBroadcast == (lambda ii:pid :: pid(ii)) && pidsCollect == pidsBroadcast;
  assert {:layer 1} Inv(CH_low, CH);
  ss := pidsBroadcast;
  rr := pidsCollect;
  i := 1;
  while (i <= n)
  invariant {:layer 0,1}{:terminates} true;
  invariant {:layer 1} 1 <= i && i <= n + 1;
  invariant {:layer 1} ss == (lambda ii:pid :: pid(ii) && ii >= i) && ss == rr;
  invariant {:layer 1} PAs == InitialPAs(i);
  {
    call s, r, ss, rr := linear_transfer(i, ss, rr);
    async call Broadcast(s);
    async call Collect(r);
    i := i + 1;
  }
  assert {:layer 1} PAs == MapAddPA(AllBroadcasts(), AllCollects());
  yield;
}

procedure {:yields}{:layer 1}{:refines "BROADCAST"} Broadcast({:linear_in "broadcast"} i:pid)
requires {:layer 1} pid(i);
{
  var j: pid;
  var v: val;
  var {:layer 1} old_CH_low: [pid][val]int;
  yield;
  call old_CH_low := Snapshot();
  call v := get_value(i);
  j := 1;
  while (j <= n)
  invariant {:layer 1}{:terminates} true;
  invariant {:layer 1} 1 <= j && j <= n+1;
  invariant {:layer 1} CH_low == (lambda jj: pid :: (if pid(jj) && jj < j then MultisetPlus(old_CH_low[jj], MultisetSingleton(value[i])) else old_CH_low[jj]));
  {
    call send(v, j);
    j := j + 1;
  }
  call intro(i);
  yield;
}

procedure {:yields}{:layer 1}{:refines "COLLECT"} Collect({:linear_in "collect"} i:pid)
requires {:layer 1} pid(i);
requires {:layer 1} Inv(CH_low, CH);
{
  var j: pid;
  var d: val;
  var v: val;
  var {:layer 1} received_values: [val]int;
  var {:layer 1} old_CH_low: [pid][val]int;
  yield; assert{:layer 1} Inv(CH_low, CH);
  call old_CH_low := Snapshot();
  call d := receive(i);
  received_values := MultisetEmpty;
  received_values[d] := received_values[d] + 1;
  // received_values := MultisetSingleton(d);
  j := 2;
  while (j <= n)
  invariant {:layer 1} 2 <= j && j <= n + 1;
  invariant {:layer 1} card(received_values) == j - 1;
  invariant {:layer 1} MultisetSubsetEq(MultisetEmpty, received_values);
  invariant {:layer 1} MultisetSubsetEq(received_values, old_CH_low[i]);
  invariant {:layer 1} CH_low == old_CH_low[i := MapSub(old_CH_low[i], received_values)];
  invariant {:layer 1} d == max(received_values);
  {
    call v := receive(i);
    if (v > d) { d := v; }
    received_values[v] := received_values[v] + 1;
    j := j + 1;
  }
  call set_decision(i, d);
  yield;
}

////////////////////////////////////////////////////////////////////////////////

procedure {:both}{:layer 1} GET_VALUE(i:pid) returns (v:val)
{
  v := value[i];
}

procedure {:both}{:layer 1} SET_DECISION({:linear_in "collect"} i:pid, d:val)
modifies decision;
{
  decision[i] := d;
}

procedure {:left}{:layer 1} SEND(v:val, i:pid)
modifies CH_low;
{
  CH_low[i][v] := CH_low[i][v] + 1;
}

procedure {:right}{:layer 1} RECEIVE(i:pid) returns (v:val)
modifies CH_low;
{
  assume CH_low[i][v] > 0;
  CH_low[i][v] := CH_low[i][v] - 1;
}

procedure {:both}{:layer 1}
LINEAR_TRANSFER(i:pid, {:linear_in "broadcast"} ss:[pid]bool, {:linear_in "collect"} rr:[pid]bool)
returns ({:linear "broadcast"} s:pid, {:linear "collect"} r:pid, {:linear "broadcast"} ss':[pid]bool, {:linear "collect"} rr':[pid]bool)
{
  assert ss[i] && rr[i];
  s, r := i, i;
  ss', rr' := ss[i := false], rr[i := false];
}

procedure {:yields}{:layer 0}{:refines "GET_VALUE"} get_value(i:pid) returns (v:val);
procedure {:yields}{:layer 0}{:refines "SET_DECISION"} set_decision({:linear_in "collect"} i:pid, d:val);
procedure {:yields}{:layer 0}{:refines "SEND"} send(v:val, i:pid);
procedure {:yields}{:layer 0}{:refines "RECEIVE"} receive(i:pid) returns (v:val);
procedure {:yields}{:layer 0}{:refines "LINEAR_TRANSFER"} linear_transfer(i:pid, {:linear_in "broadcast"} ss:[pid]bool, {:linear_in "collect"} rr:[pid]bool)
returns ({:linear "broadcast"} s:pid, {:linear "collect"} r:pid, {:linear "broadcast"} ss':[pid]bool, {:linear "collect"} rr':[pid]bool);

////////////////////////////////////////////////////////////////////////////////

function {:builtin "MapConst"} MapConstInt(int) : [val]int;
function {:builtin "MapConst"} MapConstBool(bool) : [val]bool;
function {:builtin "MapOr"} MapOr([int]bool, [int]bool) : [int]bool;
function {:builtin "MapAdd"} MapAdd([val]int, [val]int) : [val]int;
function {:builtin "MapSub"} MapSub([val]int, [val]int) : [val]int;
function {:builtin "MapLt"} MapLt([val]int, [val]int) : [val]bool;
function {:builtin "MapLe"} MapLe([val]int, [val]int) : [val]bool;

function {:builtin "MapAdd"} MapAddPA([PA]int, [PA]int) : [PA]int;

const MultisetEmpty:[val]int;
axiom MultisetEmpty == MapConstInt(0);

function {:inline} MultisetSingleton(v:val) : [val]int
{
  MultisetEmpty[v := 1]
}

function {:inline} MultisetSubsetEq(a:[val]int, b:[val]int) : bool
{
  MapLe(a, b) == MapConstBool(true)
}

function {:inline} MultisetPlus(a:[val]int, b:[val]int) : [val]int
{
  MapAdd(a, b)
}

function {:inline} MultisetMinus(a:[val]int, b:[val]int) : [val]int
{
  MapSub(a, b)
}

////////////////////////////////////////////////////////////////////////////////

function {:inline}{:linear "broadcast"} BroadcastCollector (pid:pid) : [int]bool
{
  MapConstBool(false)[pid := true]
}
function {:inline}{:linear "collect"} CollectCollector (pid:pid) : [int]bool
{
  MapConstBool(false)[pid := true]
}
function {:inline}{:linear "broadcast"} BroadcastSetCollector (pids:[pid]bool) : [int]bool
{
  pids
}
function {:inline}{:linear "collect"} CollectSetCollector (pids:[pid]bool) : [int]bool
{
  pids
}
