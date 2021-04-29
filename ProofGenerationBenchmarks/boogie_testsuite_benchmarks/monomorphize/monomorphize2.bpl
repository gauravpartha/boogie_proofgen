// RUN: %boogie -monomorphize "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/** MANUAL REWRITE: Replaced all # with H */
type Vec T;
function VecHEmpty<T>(): Vec T;
function VecHUnit<T>(t: T): Vec T;
function VecHConcat<T>(s1: Vec T, s2: Vec T): Vec T;
function VecHExtract<T>(s: Vec T, pos: int, len: int): Vec T;
function VecHUpdate<T>(s: Vec T, pos: int, t: T): Vec T;
function VecHLen<T>(s: Vec T): int;
function VecHSelect<T>(s: Vec T, pos: int): T;
function VecHIsEqual<T>(s1: Vec T, s2: Vec T): bool;
axiom  (forall<U> :: VecHLen(VecHEmpty() : Vec U) == 0);
axiom  (forall<U> e: U :: VecHLen(VecHUnit(e)) == 1);

type Set T;
function SetHEmpty<T>(): Set T;
function SetHUnit<T>(t: T): Set T;
function SetHAdd<T>(s: Set T, t: T): Set T;
function SetHRemove<T>(s: Set T, t: T): Set T;
function SetHUnion<T>(s1: Set T, s2: Set T): Set T;
function SetHIntersection<T>(s1: Set T, s2: Set T): Set T;
function SetHDifference<T>(s1: Set T, s2: Set T): Set T;
function SetHSize<T>(s: Set T): int;
function SetHContains<T>(s: Set T, t: T): bool;
function SetHIsEqual<T>(s1: Set T, s2: Set T): bool;
axiom  (forall<U> :: SetHSize(SetHEmpty() : Set U) == 0);
axiom  (forall<U> e: U :: SetHSize(SetHUnit(e)) == 1);

procedure empty_vec() returns (v: Vec int)
ensures VecHLen(v) == 0;
{
    v := VecHEmpty();
}

procedure unit_vec(e: int) returns (v: Vec int)
ensures VecHLen(v) == 1;
{
    v := VecHUnit(e);
}

procedure empty_set() returns (v: Set int)
ensures SetHSize(v) == 0;
{
    v := SetHEmpty();
}

procedure unit_set(e: int) returns (v: Set int)
ensures SetHSize(v) == 1;
{
    v := SetHUnit(e);
}

type K;

procedure empty_vec_k() returns (v: Vec K)
ensures VecHLen(v) == 0;
{
    v := VecHEmpty();
}

procedure empty_set_k() returns (v  : Set K)
ensures SetHSize(v) == 0;
{
    v := SetHEmpty();
}

