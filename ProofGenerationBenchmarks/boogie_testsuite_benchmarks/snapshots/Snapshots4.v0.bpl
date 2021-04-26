procedure  P0();
// Action: verify
implementation   P0()
{
}


procedure  P1();
// Action: verify
implementation   P1()
{
    call P2();
}


procedure  P2();
  ensures G();


procedure  P3();
// Action: verify
implementation   P3()
{
}


function  G() : bool
{
    F()
}


function  F() : bool
{
    true
}
