
object Abs:
    def abs(x: BigInt): BigInt = {
        if x < 0 then -x
        else x
    }.ensuring(res => res >= 0)
    