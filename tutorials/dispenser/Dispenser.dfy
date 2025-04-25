
module Dispenser {

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
  

  datatype State = 
    State(levels: seq<seq<int>>, coins: int, oneInserted: bool)
  
  function ValidState(s: State): bool
    {
       |s.levels| == 6 && 
      (forall x: nat | 0 <= x < |s.levels| :: |s.levels[x]| == 4) &&
      0 <= s.coins <= 500
    }

  function isInitial(s: State): bool
    requires (ValidState(s))
    ensures ValidState(s)
  {
    (forall x: nat | 0 <= x < |s.levels| :: (forall y: nat | 0 <= y < |s.levels[x]| :: s.levels[x][y] == 10)) &&
    s.coins == 0 &&
    s.oneInserted == false
  }

  function r(s1: State, a: Action): (res: Option<State>)
    requires ValidState(s1)
    requires Valid(a)
  {
    match a {
      case FirstCoin() => 
        if (!s1.oneInserted && s1.coins < 500) then
          var newS := State(s1.levels, s1.coins + 1, true);
          var r := Some(newS);
          r
         else 
          None
      case SecondCoin(levelNo, slotNo) =>
        if (s1.oneInserted && s1.coins < 500) then
          var level: seq<int> := s1.levels[levelNo];
          var amount: int := level[slotNo];
          if (amount > 0) then
            var newLevel: seq<int> := level[0..slotNo] + [level[slotNo] - 1] + level[slotNo + 1..];
            var newLevels: seq<seq<int>> := s1.levels[0..levelNo] + ([newLevel] + s1.levels[levelNo + 1..]);
            var newS := State(newLevels, s1.coins + 1, false);
            Some(newS)
          else 
            None
        else 
          None
    }
  }

  function isTraceLike(t: seq<(State, Action)>):  (res: bool)
    requires forall i: int | 0 <= i < |t| :: ValidState(t[i].0)
    requires forall i: int | 0 <= i < |t| :: Valid(t[i].1)
    decreases |t|
    {
      if |t| > 1 then
        var temp := r(t[0].0, t[0].1);
        if temp == Some(t[1].0) then
          var result := isTraceLike(t[1..]);
          result
        else
          false
      else 
        true
    }

  function isTrace(t: seq<(State, Action)>): (res: bool)
    requires forall i: int | 0 <= i < |t| :: ValidState(t[i].0)
    requires forall i: int | 0 <= i < |t| :: Valid(t[i].1)
    decreases |t|
  {
    if |t| > 0 then
      var isTraceLikeRes := isTraceLike(t[1..]);
      var result := isInitial(t[0].0) && isTraceLikeRes;
      result
    else 
      false
  }
  
  method exampleTrace() returns (res: seq<(State, Action)>)
    ensures forall i: int | 0 <= i < |res| :: ValidState(res[i].0)
    ensures forall i: int | 0 <= i < |res| :: Valid(res[i].1)
    ensures isTrace(res)
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
    var s0: State := State(levels, 0, false);
    var s1: Option<State> := r(s0, FirstCoin());
    var s2: Option<State> := r(get(s1), SecondCoin(0, 0));
    var trc: seq<(State, Action)> := [(s0, FirstCoin()), (get(s1), SecondCoin(0, 0)), (get(s2), FirstCoin())];
    return trc;
  }
}