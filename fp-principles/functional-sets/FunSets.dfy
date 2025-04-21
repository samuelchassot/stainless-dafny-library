module FunSets {
  function contains(s: int -> bool, elem: int): bool
  {
    s(elem)
  }

  function complement(s: int -> bool): (res: int -> bool)
  {
    x => !s(x)
  }

  function checkComplement(e: int, s: int -> bool): (res: bool)
    ensures res
  {
    contains(s, e) || contains(complement(s), e)
  }

  function singletonSet(elem: int): (res: int -> bool)
  {
    x => x == elem
  }

  function checkContains(s1: int -> bool, s2: int -> bool, e: int): (res: bool)
    ensures res
    {
      contains(singletonSet(e), e)
    }

  function checkSingleton(e1: int, e2: int, s: int -> bool): (res: bool)
    ensures res
  {
    e1 == e2 || (contains(singletonSet(e1), e1) && !(contains(singletonSet(e1), e2)))
  }

  function union(s: int -> bool, t: int -> bool): (res: int -> bool)
  {
    x => s(x) || t(x)
  }

  function checkUnion1(s1: int -> bool, s2: int -> bool, e: int): (res: bool)
    ensures res
  {
    (!contains(s1, e) && !contains(s2, e)) || (contains(union(s1, s2), e))
  }

  function checkUnion2(s1: int -> bool, s2: int -> bool, e: int): (res: bool)
    ensures res
  {
    (!contains(union(s1, s2), e) || contains(s1, e) || contains(s2, e))
  }

  function intersect(s: int -> bool, t: int -> bool): (res: int -> bool)
  {
    x => s(x) && t(x)
  }

  function checkBigIntersect(s1: int -> bool, s2: int -> bool, e: int): (res: bool)
    ensures res
  {
    (contains(s1, e) && contains(s2, e)) || !contains(intersect(s1, s2), e)
  }

  function diff(s: int -> bool, t: int -> bool): (res: int -> bool)
  {
    x => s(x) && !t(x)
  }

  function checkDiff(s1: int -> bool, s2: int -> bool, e: int): (res: bool)
    ensures res
  {
    !contains(diff(s1, s2), e) || (contains(s1, e) && !contains(s2, e))
  }

  function filter(s: int -> bool, p: int -> bool): (res: int -> bool)
  {
    x => s(x) && p(x)
  }

  // lemma filterIterForallCheck(a: int, s: int -> bool, p: int -> bool) returns (res: bool)
  //   ensures res
  // {
  //   var result := filter(s, p);
  //   if (a > bound()) {

  //   } else {
  //     if (result(a) && !p(a)) {

  //     } else {
  //       var _ := filterIterForallCheck(a + 1, s, p);
  //     }
  //   }
  //   iterForallCheck(a, result, p);
  // }

  function bound(): int 
  {
    1000
  }

  // function filterForallCheck(s: int -> bool, p: int -> bool): (res: bool)
  //   ensures res
  // {
  //   var result := filter(s, p);
  //   iterForallCheck(0, result, p);
  // }

  function max(x: int, y: int): (res: int)
  {
    if (x > y) then x else y
  }

  function iterForallCheck(a: int, s: int -> bool, p: int -> bool): (res: bool)
    decreases (if (a < 0) then -(a + 1) else 0) + max(0, (bound() - (a + 1)))
  {
    if (a > bound()) then 
      true
    else if (s(a) && !p(a)) then 
      false
    else 
      assert a < 0 || bound() - (a + 1) >= 0;
      iterForallCheck(a + 1, s, p)
  }
  

}