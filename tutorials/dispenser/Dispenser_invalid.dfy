
module Dispenser {

  datatype Option<T> = 
    None
  | Some(t: T)

  function get<T>(o: Option<T>): T
    requires o != None
  {
    match o {
      case None => 0 
      case Some(t) => t
    }
  }

  datatype Action = 
    FirstCoin()
  | SecondCoin(levelNo: int, slotNo: int)

    ghost predicate Valid(a: Action) 
    {
      match a {
        case FirstCoin() => true
        case SecondCoin(levelNo, slotNo) => 0 <= levelNo <= 5 && 0 <= slotNo <= 3
      }
    }
  

  class State {
    var levels: seq<seq<int>>
    var coins: int
    var oneInserted: bool

    ghost predicate Valid() 
      reads this
    {
      |levels| == 6 && 
      (forall x: nat | 0 <= x < |levels| :: |levels[x]| == 4) &&
      0 <= coins <= 500
    }

    constructor (levels: seq<seq<int>>, coins: int, oneInserted: bool)
      requires |levels| == 6
      requires (forall x: nat | 0 <= x < |levels| :: |levels[x]| == 4)
      requires 0 <= coins <= 500
      ensures this.levels == levels
      ensures this.coins == coins
      ensures this.oneInserted == oneInserted
      ensures Valid()
    {
      this.levels := levels;
      this.coins := coins;
      this.oneInserted := oneInserted;
    }
  }

  function isInitial(s: State): bool
    reads s
    requires s.Valid()
    ensures s.Valid()
  {
    (forall x: nat | 0 <= x < |s.levels| :: (forall y: nat | 0 <= y < |s.levels[x]| :: s.levels[x][y] == 10)) &&
    s.coins == 0 &&
    s.oneInserted == false
  }

  method r(s1: State, a: Action) returns (res: Option<State>)
    requires s1.Valid()
    requires Valid(a)
  {
    match a {
      case FirstCoin() => 
        if (!s1.oneInserted && s1.coins < 500) {
          var newS := new State(s1.levels, s1.coins + 1, true);
          var r := Some(newS);
          return r;
        } else {
          return None;
        }
      case SecondCoin(levelNo, slotNo) =>
        if (s1.oneInserted && s1.coins < 500) {
          var level: seq<int> := s1.levels[levelNo];
          var amount: int := level[slotNo];
          if (amount > 0) {
            var newLevel: seq<int> := level[0..slotNo] + [level[slotNo] - 1] + level[slotNo + 1..];
            var newLevels: seq<seq<int>> := s1.levels[0..levelNo] + ([newLevel] + s1.levels[levelNo + 1..]);
            var newS := new State(newLevels, s1.coins + 1, false);
            return Some(newS);
          } else {
            return None;
          }
        } else {
            return None;
        }
    }
  }

  method isTraceLike(t: seq<(State, Action)>):  (res: bool)
    requires forall i: int | 0 <= i < |t| :: t[i].0.Valid()
    requires forall i: int | 0 <= i < |t| :: Valid(t[i].1)
    decreases |t|
    {
      if |t| > 1 {
        var temp := r(t[0].0, t[0].1);
        if temp == Some(t[1].0) {
          var result := isTraceLike(t[1..]);
          return result;
        } else {
          return false;
        }
      } else {
        return true;
      }
    }

  method isTrace(t: seq<(State, Action)>) returns (res: bool)
    requires forall i: int | 0 <= i < |t| :: t[i].0.Valid()
    requires forall i: int | 0 <= i < |t| :: Valid(t[i].1)
    decreases |t|
  {
    if |t| > 0 {
      var isTraceLikeRes := isTraceLike(t[1..]);
      var result := isInitial(t[0].0) && isTraceLikeRes;
      return result;
    } else {
      return false;
    }
  }
  
  method exampleTrace() returns (res: seq<(State, Action)>)
    ensures isTrace(res) // WE CANNOT CALL METHOD IN THE ENSURES CLAUSE!!!!!!!!!!!!!!!!!!!
  {
    var b10: int := 10;
    var levels := [
      [b10, b10, b10, b10],
      [b10, b10, b10, b10],
      [b10, b10, b10, b10],
      [b10, b10, b10, b10],
      [b10, b10, b10, b10],
      [b10, b10, b10, b10]
    ];
    var s0: State := new State(levels, 0, false);
    var s1: Option<State> := r(s0, FirstCoin());
    var s2: Option<State> := r(get(s1), SecondCoin(0, 0));
    var trc: seq<(State, Action)> := [(s0, FirstCoin()), (get(s1), SecondCoin(0, 0)), (get(s2), FirstCoin())];
    return trc;
  }
}