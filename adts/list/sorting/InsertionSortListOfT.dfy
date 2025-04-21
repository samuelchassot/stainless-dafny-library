module Sorted {
  trait Ordering<T> {
    function compare(x: T, y: T): int

    function sign(x: int): int {
      if x < 0 then -1 else if x > 0 then 1 else 0
    }

    lemma InverseLaw(x: T, y: T)
      ensures sign(compare(x, y)) == -sign(compare(y, x))

    lemma TransitiveLaw(x: T, y: T, z: T)
      ensures (compare(x, y) > 0 && compare(y, z) > 0) ==> compare(x, z) > 0

    lemma ConsistentLaw(x: T, y: T, z: T)
      ensures (compare(x, y) == 0) ==> (sign(compare(x, z)) == sign(compare(y, z)))
  }

  lemma lemmaTest<T>(x: T, y: T, ordering: Ordering<T>)
    requires ordering.compare(x, y) > 0
    ensures ordering.compare(y, x) < 0
  {
    ordering.InverseLaw(x, y);
  }

  function isSorted<T>(l: seq<T>, ordering: Ordering<T>): bool
    decreases |l|
  {
    if |l| < 2 then 
      true
    else 
      ordering.compare(l[0], l[1]) <= 0 && isSorted(l[1..], ordering)
  }

  function insert<T>(l: seq<T>, x: T, ordering: Ordering<T>): (res: seq<T>)
    requires isSorted(l, ordering)
    ensures isSorted(res, ordering) && |res| == |l| + 1
  {
    if |l| == 0 then 
      [x]
    else if ordering.compare(x, l[0]) <= 0 then 
      [x] + l
    else 
      (ordering.InverseLaw(x, l[0]); [l[0]] + insert(l[1..], x, ordering))
  }

  function sort<T>(l: seq<T>, ordering: Ordering<T>): (res: seq<T>)
    ensures isSorted(res, ordering) && |res| == |l|
  {
    if |l| == 0 then 
      []
    else 
      insert(sort(l[1..], ordering), l[0], ordering)
  }
}