// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// ###########################################################################
// Linear permissions

type {:linear "lin"} Perm = int;

function {:inline} perm (p : int) : bool
{ p == 0 }

// ###########################################################################
// Global shared variables

var {:layer 7,9} x : int;
var {:layer 7,9} y : int;

// ###########################################################################
// Main

procedure {:yields}{:layer 9} main ({:linear_in "lin"} p : int)
requires {:layer 9} perm(p) && x == y;
{
  async call {:sync} Server_Inc(p);
}

// ###########################################################################
// Event Handlers

procedure {:yields}{:left}{:layer 9} Server_Inc ({:linear_in "lin"} p : int)
requires {:layer 9} perm(p) && x == y;
ensures  {:layer 9} x == old(x) + 1;
modifies x;
{
  call Yield_8();
  async call {:sync} AsyncInc(p);
  call Yield_8();
}

procedure {:yields}{:left}{:layer 9} AsyncInc ({:linear_in "lin"} p : int)
requires {:layer 9} perm(p) && x == y;
ensures  {:layer 9} x == old(x) + 1;
modifies x;
{
  call Yield_8();
  call inc_x_perm(p);
  async call {:sync} Client_IncDone(p);
  call Yield_8();
}

procedure {:yield_invariant}{:layer 8} Yield_8 ();

// ###########################################################################
// Abstracted low-level atomic actions (i.e., enriched with permissions)

procedure {:left}{:layer 9} inc_x_perm_atomic ({:linear "lin"} p : int)
modifies x;
{ assert perm(p); x := x + 1; }

procedure {:left}{:layer 9} Client_IncDone_atomic ({:linear_in "lin"} p : int)
{ assert perm(p) && x == y + 1; }

procedure {:yields}{:layer 8}{:refines "inc_x_perm_atomic"} inc_x_perm ({:linear "lin"} p : int)
{
  call inc_x();
}

procedure {:yields}{:layer 8}{:refines "Client_IncDone_atomic"} Client_IncDone ({:linear_in "lin"} p : int)
{
  call Assertion();
}

// ###########################################################################
// Low-level atomic actions

procedure {:atomic}{:layer 8} inc_x_atomic ()
modifies x;
{ x := x + 1; }

procedure {:atomic}{:layer 8} Assertion_atomic ()
{ assert x == y + 1; }

procedure {:yields}{:layer 7}{:refines "inc_x_atomic"} inc_x ();
procedure {:yields}{:layer 7}{:refines "Assertion_atomic"} Assertion ();
