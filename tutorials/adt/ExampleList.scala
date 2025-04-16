
object ADTList:
  sealed abstract class List[C]
  case class Nil[C]() extends List[C]
  case class Cons[C](head: C, tail: List[C]) extends List[C]

  def isEmpty[C](l: List[C]): Boolean = {
    l match {
      case Nil() => true
      case _ => false
    }
  }

  def head[C](l: List[C]): C = {
    require(!isEmpty(l))
    l match {
      case Cons(h, _) => h
    }
  }

  def tail[C](l: List[C]): List[C] = {
    require(!isEmpty(l))
    l match {
      case Cons(_, t) => t
    }
  }

  def contains[C](l: List[C], e: C): Boolean = {
    l match {
      case Nil() => false
      case Cons(h, t) => if (h == e) true else contains(t, e)
    }
  }

  def max(l: List[BigInt]): BigInt = {
    require(!isEmpty(l))
    l match {
      case Cons(h, Nil()) => h
      case Cons(h, t) => {
        val m = max(t)
        if (h > m) h else m
      }
    }
  }.ensuring(res => contains(l, res))

  def lemmaMaxSoundness(l: List[BigInt], e: BigInt): Unit = {
    require(contains(l, e))
    l match {
      case Cons(h, t) => if (h != e) then lemmaMaxSoundness(t, e)
    }
  }.ensuring(_ => max(l) >= e)
end ADTList