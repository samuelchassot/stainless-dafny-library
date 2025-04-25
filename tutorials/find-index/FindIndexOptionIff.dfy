module FindIndexOptionIff {
  datatype Option<T> = 
    None
  | Some(t: T)

  function get<T>(o: Option<T>): T
    requires o != None
  {
    match o {
      case Some(t) => t
    }
  }

  function notPresent<T(==)>(upto: int, a: array<T>, t: T): bool
    reads a
    requires 0 <= upto < a.Length
  {
    a[upto] != t && 
    (upto == 0 || notPresent(upto - 1, a, t))
  }

  method findIndexOpt<T(==)>(a: array<T>, t: T) returns (res: Option<int>)
    requires a.Length < 65536
    ensures (
      match res {
        case None => a.Length == 0 || notPresent(a.Length - 1, a, t)
        case Some(i) => 0 <= i < a.Length && a[i] == t
      }
    )
  {
    var N: int := a.Length;
    var i: int := 0;

    if 0 < N {
      while i < N 
        invariant 0 <= i <= N
        invariant i == 0 || notPresent(i - 1, a, t)
        decreases N - i
      {
        if a[i] == t {
            assert 0 <= i <= N && a.Length == N && (i == 0 || notPresent(i - 1, a, t));
            assert 0 <= i && i < a.Length && a[i] == t;
          return Some(i);
        }
        i := i + 1;
        assert 0 <= i <= N && a.Length == N && (i == 0 || notPresent(i - 1, a, t));
      }
      return None;
    } else {
      return None;
    }

  }
}