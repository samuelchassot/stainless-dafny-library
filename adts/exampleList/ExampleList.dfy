
datatype List<C> = 
  Nil
| Cons(C, List<C>)

function isEmpty<C>(l: List<C>): bool 
{
  match l {
    case Nil => true
    case Cons(_, _) => false
  } 
}

function head<C>(l: List<C>): C
  requires !isEmpty(l)
{
  match l {
    case Cons(h, _) => h
  }
}

function tail<C>(l: List<C>): List<C>
  requires !isEmpty(l)
{
  match l {
    case Cons(_, t) => t
  }
}

function contains<C(==)>(l: List<C>, x: C): bool
{
  match l {
    case Nil => false
    case Cons(h, t) => if (h == x) then true else contains(t, x)
  }
}

function max(l: List<nat>): (result: nat)
  requires !isEmpty(l)
  ensures contains(l, result)
{
  match l {
    case Nil => 0
    case Cons(h, t) => if (isEmpty(t)) then h else if (h > max(t)) then h else max(t)
  }
}

method lemmaMaxSoundness(l: List<nat>, x: nat)
  requires contains(l, x)
  ensures max(l) >= x
{
  match l {
    case Cons(h, t) => if (h != x) {
      lemmaMaxSoundness(t, x);
    }
  }
}

lemma lemmaMaxSoundnessL(l: List<nat>, x: nat)
  requires contains(l, x)
  ensures max(l) >= x
{
  match l {
    case Cons(h, t) => if (h != x) {
      lemmaMaxSoundnessL(t, x);
    }
  }
}