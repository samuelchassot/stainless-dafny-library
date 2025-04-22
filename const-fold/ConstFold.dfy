
module ConstFold {

  datatype Expr = 
    Number(int)
  | Var(string)
  | Add(e1: Expr, e2: Expr)
  | Minus(e1: Expr, e2: Expr)
  | Mul(e1: Expr, e2: Expr)

  type Env = string -> int

  function zeroEnv(): Env 
  {
    x => 0
  }

  function evaluate(ctx: Env, e: Expr): (res: int)
  {
    match e {
      case Number(value) => value
      case Var(name) => ctx(name)
      case Add(e1, e2) => evaluate(ctx, e1) + evaluate(ctx, e2)
      case Minus(e1, e2) => evaluate(ctx, e1) - evaluate(ctx, e2)
      case Mul(e1, e2) => evaluate(ctx, e1) * evaluate(ctx, e2)
    }
  } 
    

  function zeroExpr(e: Expr): (res: bool)
  {
    match e
      case Number(value) => value == 0
      case Var(_) => false
      case Add(e1, e2) => zeroExpr(e1) && zeroExpr(e2)
      case Minus(e1, e2) => zeroExpr(e1) && zeroExpr(e2)
      case Mul(e1, e2) => zeroExpr(e1) || zeroExpr(e2)
  } 

  lemma lemmaL(ctx: Env, e: Expr)
    requires zeroExpr(e)
    ensures evaluate(ctx, e) == 0
    {
    match e
      case Number(_) => 
      case Var(_) => 
      case Add(e1, e2) => lemmaL(ctx, e1); lemmaL(ctx, e2);
      case Minus(e1, e2) => lemmaL(ctx, e1); lemmaL(ctx, e2);
      case Mul(e1, e2) => 
        if (zeroExpr(e1)) {
          lemmaL(ctx, e1);
        } else {
          lemmaL(ctx, e2);
        }
    }

  function mirror(e: Expr, anyCtx: Env): (res: Expr)
    ensures evaluate(anyCtx, res) == evaluate(anyCtx,e)
  {
    match e
      case Number(value) => e
      case Var(name) => e
      case Add(e1, e2) => Add(mirror(e2, anyCtx), mirror(e1, anyCtx))
      case Minus(e1, e2) => Minus(mirror(e1, anyCtx), mirror(e2, anyCtx))
      case Mul(e1, e2) => Mul(mirror(e2, anyCtx), mirror(e1, anyCtx))
  }
  

  trait SoundSimplifier{
    function apply(e: Expr, anyCtx: Env): (res: Expr)
      ensures evaluate(anyCtx, res) == evaluate(anyCtx,e)
  }
  
  // val mirSimp = new SoundSimplifier:
  //   override def apply(e: Expr, anyCtx: Env) = mirror(e)(anyCtx)
  
  class MirrorSimplifier extends SoundSimplifier {
    function apply(e: Expr, anyCtx: Env): (res: Expr)
      ensures evaluate(anyCtx, res) == evaluate(anyCtx,e)
    { 
      mirror(e, anyCtx)
    }
  }

  function constfold1(e: Expr, anyCtx: Env): (res: Expr)
    ensures evaluate(anyCtx, res) == evaluate(anyCtx,e)
  {
    match e
      case Add(Number(n1), Number(n2))   => Number(n1 + n2)
      case Minus(Number(n1), Number(n2)) => Number(n1 - n2)
      case Mul(Number(n1), Number(n2))   => Number(n1 * n2)
      case e                             => e
  }

  class ConstFoldSimplifier extends SoundSimplifier {
    constructor Init() {}

    function apply(e: Expr, anyCtx: Env): (res: Expr)
      ensures evaluate(anyCtx, res) == evaluate(anyCtx,e)
    { 
      constfold1(e, anyCtx)
    }
  }

  function mapExpr(e: Expr, f: SoundSimplifier, anyCtx: Env): (res: Expr)
    ensures evaluate(anyCtx, res) == evaluate(anyCtx, e)
  {
   var mapped := match e {
      case Number(_)     => e
      case Var(_)        => e
      case Add(e1, e2)   => Add(mapExpr(e1, f, anyCtx), mapExpr(e2, f, anyCtx))
      case Minus(e1, e2) => Minus(mapExpr(e1, f, anyCtx), mapExpr(e2, f, anyCtx))
      case Mul(e1, e2)   => Mul(mapExpr(e1, f, anyCtx), mapExpr(e2, f, anyCtx))
    };

    f.apply(mapped, anyCtx) 
  }

  method constFold(e: Expr, anyCtx: Env) returns (res: Expr)
    ensures evaluate(anyCtx, res) == evaluate(anyCtx, e)
  {
    var simp := new ConstFoldSimplifier.Init();
    var r := mapExpr(e, simp, anyCtx);
    return r;
  }

}