
module Find {
  function interval(a: array<int>, lo: int, hi: int): bool {
    0 <= lo <= hi <= a.Length
  }

  function existsIn(a: array<int>, lo: int, hi: int, x: int): bool
    requires interval(a, lo, hi)
    reads a
    decreases hi - lo
  {
    !(lo == hi) &&
    ((a[hi - 1] == x) || existsIn(a, lo, hi - 1, x))
  }

  lemma existsInCombinedInterval(a: array<int>, lo: int, mid: int, hi: int, x: int)
    requires interval(a, lo, mid)
    requires interval(a, mid, hi)
    ensures  (existsIn(a, lo, hi, x) == (existsIn(a, lo, mid, x) || existsIn(a, mid, hi, x)))
    decreases hi - mid
  {
    // wow automatic induction!!
  }

  method find(a: array<int>, lo: int, hi: int, x: int) returns (res: int)
    requires interval(a, lo, hi)
    ensures (lo <= res < hi && a[res] == x) || (res == -1 && !existsIn(a, lo, hi, x))
  {
    var i: int := lo;
    while (i < hi && a[i] != x) 
      decreases hi - i
      invariant lo <= i <= hi && !existsIn(a, lo, i, x)
    {
      i := i + 1;
    }
    if i < hi {
      return i;
    } else {
      return -1;
    }
  }

  function search1(a: array<int>, lo: int, hi: int, x: int): (res: int)
    requires interval(a, lo, hi)
    reads a
    ensures (lo <= res < hi && a[res] == x) || res == -1
    decreases hi - lo
    {
      if lo < hi then 
        var i: int := lo + (hi - lo) / 2;
        var seeing := a[i];
        if x == seeing then i 
        else if x < seeing then search1(a, lo, i, x)
        else search1(a, i + 1, hi, x)
       else -1
    }

  method search2(a: array<int>, lo: int, hi: int, x: int) returns (res:int)
    requires interval(a, lo, hi)
    ensures (lo <= res < hi && a[res] == x) || res == -1
  {
    var lo0 := lo;
    var hi0 := hi;
    var result := -1;
    assert hi <= a.Length;
    while result == -1 && lo0 < hi0
      decreases hi0 - lo0
      invariant lo <= lo0 <= hi0 <= hi && ((lo <= result < hi && a[result] == x) || result == -1)
      {
        var i: int := lo0 + (hi0 - lo0) / 2;
        var seeing := a[i];
        if x == seeing {
          result := i;
          lo0 := lo0 + 1; // mandatory to prove the decreases clause
        } else if x < seeing {
          hi0 := i;
        } else {
          lo0 := i + 1;
        }
      }
      return result;
  }

  function isSorted(a: array<int>, lo: int, hi: int): bool 
    requires interval(a, lo, hi)
    reads a
    decreases hi - lo
  {
    lo == hi ||
    lo + 1 == hi ||
    (a[lo] <= a[lo + 1] && isSorted(a, lo + 1, hi))
  }

  lemma isSortedAt(a: array<int>, lo: int, hi: int, i: int)
    requires interval(a, lo, hi)
    requires lo <= i < hi
    requires i < hi 
    requires i + 1 < hi 
    requires isSorted(a, lo, hi)
    decreases i - lo
    ensures a[i] <= a[i + 1]
  {
    // wow automatic induction!!
  }
    
  lemma isSortedSubinterval(a: array<int>, lo: int, lo1: int, hi1: int, hi: int)
    requires interval(a, lo, hi)
    requires isSorted(a, lo, hi)
    requires interval(a, lo1, hi1)
    requires lo <= lo1  
    requires hi1 <= hi
    decreases hi1 - lo1
    ensures isSorted(a, lo1, hi1)
    {
      if lo1 < hi1 {
        isSortedSubinterval(a, lo, lo1 + 1, hi1, hi);
        if lo1 < hi && lo1 + 1 < hi {
          isSortedAt(a, lo, hi, lo1);
        }
      }
    }

    lemma lessWhenSorted(a: array<int>, lo: int, i: int, hi: int, x: int)
      requires interval(a, lo, hi)
      requires isSorted(a, lo, hi)
      requires lo <= i < hi
      requires x < a[i]
      decreases hi - i
      ensures !existsIn(a, i, hi, x)
    {
      if i + 1 < hi {
        isSortedAt(a, lo, hi, i);
        lessWhenSorted(a, lo, i + 1, hi, x);
        existsInCombinedInterval(a, i, i + 1, hi, x);
      }
    }

    lemma moreWhenSorted(a: array<int>, lo: int, i: int, hi: int, x: int)
      requires interval(a, lo, hi)
      requires isSorted(a, lo, hi)
      requires lo <= i < hi
      requires x > a[i]
      decreases i - lo
      ensures !existsIn(a, lo, i + 1, x)
    {
      if lo < i {
        isSortedAt(a, lo, hi, i - 1);
        moreWhenSorted(a, lo, i - 1, hi, x);
        existsInCombinedInterval(a, i - 1, i, hi, x);
      }
    } 

    function search4(a: array<int>, lo: int, hi: int, x: int): (res: int)
      reads a
      requires interval(a, lo, hi)
      requires isSorted(a, lo, hi)
      ensures (lo <= res < hi && a[res] == x) || ((res == -1) && !existsIn(a, lo, hi, x))
      decreases hi - lo
    {
      if lo < hi then
        var i := lo + (hi - lo) / 2;
        assert i <= hi;
        var seeing := a[i];
        if x == seeing then
          i
        else 
          if x < seeing then
            // Way to call lemmas in Unary Expression, in an expression
            // with (lemma(x); result)
            (isSortedSubinterval(a, lo, lo, i, hi);
            lessWhenSorted(a, lo, i, hi, x);
            existsInCombinedInterval(a, lo, i, hi, x);
            search4(a, lo, i, x))
          else
            (isSortedSubinterval(a, lo, i + 1, hi, hi);
            moreWhenSorted(a, lo, i, hi, x);
            existsInCombinedInterval(a, lo, i + 1, hi, x);
            search4(a, i+1, hi, x))
      else -1
    }

}