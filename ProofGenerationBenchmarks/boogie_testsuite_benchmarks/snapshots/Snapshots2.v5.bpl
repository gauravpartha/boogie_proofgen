procedure  P0();
requires F0();
ensures F0();
// Action: verify (procedure changed)
implementation   P0()
{
    call P0();
}


function  F0() : bool
{
    false
}
