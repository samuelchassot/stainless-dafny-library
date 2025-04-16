function xor2(x: bool, y: bool): bool
{
  (x && !y) || (!x && y)
}

function xor3(x: bool, y: bool, z: bool): (result: bool)
{
  xor2(xor2(x, y), z)
}

type Digits = seq<bool>

function zero(): Digits {
  []
}

lemma addCom0(x: int, y: int)
  ensures x + y == y + x
  {
    
  }

function add(x: Digits, y: Digits, carry: bool): Digits 
  requires |x| == |y|
{
  if |x| == 0 then 
    if carry then [true] else []
  else 
    [xor3(x[0], y[0], carry)] + add(x[1..], y[1..], (x[0] && y[0]) || (x[0] && carry) || (y[0] && carry))
}

lemma addCom(x: Digits, y: Digits, carry: bool)
  requires |x| == |y|
  ensures add(x, y, carry) == add(y, x, carry)
{
  if |x| == 0 {} 
  else {
    addCom(x[1..], y[1..], (x[0] && y[0]) || (x[0] && carry) || (y[0] && carry));
  }
}