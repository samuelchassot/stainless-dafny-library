
class Stack<T> {
  constructor () { data := []; }
  var data: seq<T>
  
  function list(): seq<T> 
    reads this
  {
    data
  }

  method push(a: T)
    modifies this
    ensures list() == [a] + old(list())
  {
    data := [a] + data;
  }

  method pop() returns (res: T)
    modifies this
    requires |list()| > 0
    ensures res == old(list())[0]
    ensures list() == old(list())[1..]
  {
    var a := list()[0];
    data := list()[1..];
    res := a;
  }
}

method pushTwo(s: Stack<int>, a: int, b: int) returns (res: int)
  modifies s
  ensures res == a
{
  s.push(b);
  s.push(a);
  res := s.pop();
}

method pushTwoPopTwo(s1: Stack<int>, s2: Stack<int>)
  modifies s1, s2
{
  s1.push(1);
  s2.push(2);
  var v1 := s1.pop();
  var v2 := s2.pop();
}

method callTwoStacks(s: Stack<int>)
  modifies s
{
  pushTwoPopTwo(s, s);
}