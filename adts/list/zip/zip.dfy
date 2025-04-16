
datatype List<T> = 
  Nil
  | Cons(T, List<T>)

function mapL<T, U>(l: List<T>, f: T -> U): List<U>
{
  match l {
    case Nil => Nil
    case Cons(h, t) => Cons(f(h), mapL(t, f))
  }
}

function size<T>(l: List<T>): nat
{
  match l {
    case Nil => 0
    case Cons(_, t) => 1 + size(t)
  }
}

lemma sizeFact<T>(l: List<T>)
  ensures size(l) != -1
{}

function xs(): List<int>
{
  Cons(1, Cons(2, Cons(3, Nil)))
}

function zip(xs: List<int>, ys: List<bool>): (res: List<(int, bool)>)
  requires size(xs) == size(ys)
  ensures mapL(res, (x: (int, bool)) => x.0) == xs
  ensures mapL(res, (x: (int, bool)) => x.1) == ys
{
  match (xs, ys) {
    case (Nil, Nil) => Nil
    case (Cons(x, xs), Cons(y, ys)) => Cons((x, y), zip(xs, ys))
  }
}

function zipL(xs: List<int>, ys: List<bool>): (res: List<(int, bool)>)
  requires size(xs) <= size(ys)
  ensures mapL(res, (x: (int, bool)) => x.0) == xs
{
  match (xs, ys) {
    case (Cons(x, xs), Cons(y, ys)) => Cons((x, y), zipL(xs, ys))
    case _ => Nil
  }
}