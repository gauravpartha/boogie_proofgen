procedure  P0();
ensures G();
// Action: verify
implementation   P0()
{
}


function  F() : bool
{
    true
}


function  G() : bool
{
    F()
}
