function abs(x: int): int;
axiom (forall x: int :: ( 0<= x ==> abs(x) == x) && ( (!(0 <= x)) ==> abs(x) == -x));
function divt(int, int): int;
function modt(int, int): int;
axiom (forall a,b: int :: divt(a,b)*b + modt(a,b) == a);
axiom (forall a,b: int ::
  (0 <= a ==> 0 <= modt(a,b) && modt(a,b) < abs(b)) &&
  (a < 0 ==> -abs(b) < modt(a,b) && modt(a,b) <= 0));
function dive(int, int): int;
function mode(int, int): int;
axiom (forall a,b: int :: dive(a,b)*b + mode(a,b) == a);
axiom (forall a,b: int :: 0 <= mode(a,b) && mode(a,b) < abs(b));
procedure T_from_E(a,b: int) returns (q,r: int)
  requires b != 0;
  ensures q*b + r == a;
  ensures 0 <= a ==> 0 <= r && r < abs(b);
  ensures a < 0 ==> -abs(b) < r && r <= 0;
{
  var qq,rr: int;
  qq := dive(a,b);
  rr := mode(a,b);
  if(0 <= a || rr == 0) {
    q := qq;
  } else {
    if (0<=b) {
      q := qq+1;
    } else {
      q := qq-1;
    }
  }
  if (0 <= a || rr == 0) {
    r := rr;
  } else {
    if(0 <= b) {
      r := rr-b;
    } else {
      r := rr+b;
    }
  }
  assume  true;
}
procedure E_from_T(a,b: int) returns (q,r: int)
  requires b != 0;
  ensures q*b + r == a;
  ensures 0 <= r;
  ensures r < abs(b);
{
  var qq,rr: int;
  qq := divt(a,b);
  rr := modt(a,b);
  if(0 <= rr) {
    q := qq;
  } else {
    if (0< b) {
      q := qq-1;
    } else {
      q := qq+1;
    }
  }
  if (0 <= rr) {
    r := rr;
  } else {
    if(0 < b) {
      r := rr+b;
    } else {
      r := rr-b;
    }
  }
}
