// Z3 4.1: /trace /proverOpt:O:smt.mbqi=true /proverOpt:O:smt.relevancy=0
function  xor(a: bool, b: bool) returns (bool)  { (!a && b) || (a && !b) }

procedure Incorrect_A(
     a: bool,  b: bool)
returns ( ap: bool,  bp: bool)
  ensures xor(ap, bp) == xor(a, b);
{
   ap := a;
   bp := b;
}

procedure Incorrect_B(
     a: bool,  b: bool)
returns ( ap: bool,  bp: bool)
  ensures xor(ap, bp) == xor(a, b);
{
   ap := a;
   bp := b;
}

procedure Incorrect_X(
     a: bool,  b: bool)
returns ( ap: bool,  bp: bool)
  ensures xor(ap, bp) == xor(a, b);
{
   ap := a;
   bp := b;
}

procedure Correct_A(
     a: bool,  b: bool)
returns ( ap: bool,  bp: bool)
  ensures xor(ap, bp) == xor(a, b);
{
   havoc ap;
   bp := xor(xor(ap, a), b);
}

procedure Correct_B(
     a: bool,  b: bool)
returns ( ap: bool,  bp: bool)
  ensures xor(ap, bp) == xor(a, b);
{
   havoc ap;
   bp := xor(xor(ap, a), b);
}

procedure Correct_X(
     a: bool,  b: bool)
returns ( ap: bool,  bp: bool)
  ensures xor(ap, bp) == xor(a, b);
{
   havoc ap;
   bp := xor(xor(ap, a), b);
}

