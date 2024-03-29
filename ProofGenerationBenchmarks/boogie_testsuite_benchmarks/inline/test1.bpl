// RUN: %boogie -inline:spec -print:- -env:0 -printInlined "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure Main()
{

	var x:int;
	var y:int;

	x := 1;
	y := 0;

	call x := inc(x, 5);
	call y := incdec(x, 2);

	assert(x - 1 == y);	

}

procedure  incdec(x:int, y:int) returns (z:int)
	ensures z == x + 1 - y;
{
	z := x;
	z := x + 1;
	call z := dec(z, y);
	
	return;
	
}

procedure  inc(x:int, i:int) returns (y:int)
	ensures y == x + i;
{
	y := x;
	y := x + i;
	return;
	
}

procedure  dec(x:int, i:int) returns (y:int)
	ensures y == x - i;
{
	y := x;
	y := x - i;
	return;
	
}