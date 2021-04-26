procedure  P0();
requires F0();
// Action: verify (function changed)
implementation   P0()
{
    call P0();
}


function  F0() : bool
{
    false
}
