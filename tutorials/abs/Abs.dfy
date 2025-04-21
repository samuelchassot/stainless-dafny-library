module Abs {
    function abs(x: int): (res: int)
        ensures res >= 0
    {
        if x < 0 then -x else x
    }
}