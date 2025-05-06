module StrictlyOrderedList {
    function last(l: seq<int>): int
        requires |l| > 0
    {
        l[|l| - 1]
    }

    lemma concatLast(left: seq<int>, right: seq<int>)
      ensures (
        var newL := left + right;
        |right| > 0 ==> (last(newL) == last(right))
      )
    {
        
    }

    lemma addLast(left: seq<int>, elem: int)
        ensures (
            var newL := left + [elem];
            |left| > 0 ==> (last(newL) == elem)
        )
    {
        
    }

    lemma concatElem(left: seq<int>, elem: int, right: seq<int>)
      ensures left + ([elem] + right) == (left + [elem]) + right
    {
        
    }

    opaque function isInorder(l: seq<int>): (res: bool)
        ensures res == forall i: int, j: int | 0 <= i < j < |l| :: l[i] < l[j]
        // ensures res ==> |l| <= 1 || isInorder(l[1..])
        decreases l
    {
        if |l| >= 2 then 
            if l[0] >= l[1] then false else isInorder(l[1..])
        else if |l| > 0 then 
            isInorder(l[1..])
        else 
            true
    }

    lemma inOrderSpread(xs: seq<int>, y: int)
        ensures isInorder(xs + [y]) == (
                        isInorder(xs) &&
                        (|xs| == 0 || last(xs) < y)
                    )
    {
        reveal isInorder;
        if |xs| == 0 {
            assert isInorder(xs + [y]) == (
                        isInorder(xs) &&
                        (|xs| == 0 || last(xs) < y));
        } else {
            inOrderSpread(xs[1..], y);
            assert isInorder(xs[1..] + [y]) == (
                        isInorder(xs[1..]) &&
                        (|xs[1..]| == 0 || last(xs[1..]) < y));
            assert xs == [xs[0]] + xs[1..];
            concatLast([xs[0]], xs[1..]);
            assert |xs| == 1 || last(xs) == last(xs[1..]);
            if |xs| >= 2 {
                assert last(xs) == last(xs[1..]);
                if !isInorder(xs[1..] + [y]) {
                    // notInorderAddHeadPreserves(xs[1..] + [y], xs[0]);
                    reveal isInorder;
                    assert xs + [y] == ([xs[0]] + xs[1..]) + [y];
                    assert xs + [y] == [xs[0]] + (xs[1..] + [y]);
                    assert !isInorder(xs + [y]);
                } else {
                    assert isInorder(xs[1..] + [y]);
                    if isInorder(xs) {
                        assert xs + [y] == ([xs[0]] + xs[1..]) + [y];
                        assert xs + [y] == [xs[0]] + (xs[1..] + [y]);
                        reveal isInorder;
                        assert xs[0] < xs[1];
                        assert isInorder(xs + [y]);
                    } else {
                        reveal isInorder;
                    }
                }
            } else {
                assert |xs| == 1;
                reveal isInorder;
                if xs[0] < y {
                    assert xs + [y] == [xs[0]] + [y];
                    assert xs + [y] == [xs[0], y];
                    assert |[xs[0], y]| == 2;
                    assert isInorder(xs + [y]) == (isInorder([y]));
                    assert isInorder([y]) == true;
                    assert isInorder(xs + [y]);
                } else {
                    reveal isInorder;
                    assert !isInorder(xs + [y]);
                }
            }
        }
    }

    // Why is it timing out? ->  I had to make the isInorder function opaque
    lemma inOrderSpreadL(xs: seq<int>, ys: seq<int>)
        ensures   isInorder(xs + ys) == (isInorder(xs) &&
                  isInorder(ys) &&
                        (|xs| == 0 || |ys| == 0 || last(xs) < ys[0])
                    )
        decreases |xs|
    {
        if |xs| == 0 {
            assert xs + ys == ys;
            assert isInorder(xs + ys) == isInorder(ys);
            reveal isInorder(xs);
            assert isInorder(xs);
        } else {
            assert |xs| >= 1;
            inOrderSpreadL(xs[1..], ys);
            assert isInorder(xs[1..] + ys) == (isInorder(xs[1..]) && isInorder(ys) && (|xs[1..]| == 0 || |ys| == 0 || last(xs[1..]) < ys[0]));
            if isInorder(xs) {
                assert isInorder(xs[1..]);
                assert isInorder(xs[1..] + ys) == isInorder(xs + ys);
            } else {
                assert !isInorder(xs[1..]);
                assert !isInorder(xs);
                assert xs + ys == ([xs[0]] + xs[1..]) + ys;
                assert !isInorder(xs + ys);
                
            }
        }
    }
}