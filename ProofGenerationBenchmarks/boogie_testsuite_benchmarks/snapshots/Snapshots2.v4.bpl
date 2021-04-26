procedure  P0();
requires F0();
// Action: skip
implementation   P0()
{
    call P0();
}


function  F0() : bool
{
    false
}
