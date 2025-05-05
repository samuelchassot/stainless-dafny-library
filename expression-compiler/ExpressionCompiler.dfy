module ExprCompiler {
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

  lemma check(b: bool)
  requires b
  ensures b
  {

  }

  datatype Binary = 
    Minus() 
    | Plus() 
    | Times()
  
  function apply(b: Binary, x: int, y: int): (res: int)
  {
    match b {
      case Minus() => x - y
      case Plus() => x + y
      case Times() => x * y
    }
  }

  datatype Expr = 
    Var(str: string)
    | ConstExpr(c: int)
    | BinExpr(left: Expr, b: Binary, right: Expr)

  type Value = int
  type Env = string -> Value

  function eval(en: Env, expr: Expr): (res: Value)
  {
    match expr 
      case ConstExpr(c) => c
      case Var(str) => en(str)
      case BinExpr(left, b, right) => 
        var l := eval(en, left);
        var r := eval(en, right);
        var res := apply(b, l, r);
        res
  } 

  datatype Instr = 
    Push(c: int)
    | Load(s: string)
    | BinOp(b: Binary)
  
  type Bytecodes = seq<Instr>
  type Stack = seq<Value>

  function push(v: Value, s: Stack): Stack
  {
    [v] + s
  }

  function run(bs: Bytecodes, en: Env, stack: Stack): Option<Stack>
  {
    if |bs| == 0 then Some(stack)
    else 
      var bs1 := bs[1..];
      match bs[0] {
        case Push(c) => run(bs1, en, push(c, stack))
        case Load(s) => run(bs1, en, push(en(s), stack))
        case BinOp(b) =>
          if |stack| < 2 then None()
          else 
            var v1 := stack[0];
            var v2 := stack[1];
            var stack1 := stack[2..];
            var res := apply(b, v2, v1);
            run(bs1, en, push(res, stack1)) 
      }
  }

  function compile(expr: Expr): (res: Bytecodes)
  {
    match expr {
      case ConstExpr(c) => [Push(c)]
      case Var(str) => [Load(str)]
      case BinExpr(left, b, right) => 
        var l := compile(left);
        var r := compile(right);
        l + r + [BinOp(b)]
    }
  }

  lemma assoc4<A>(aas: seq<A>, bs: seq<A>, cs: seq<A>, ds: seq<A>)
    ensures (aas + (bs + cs)) + ds == aas + bs + cs + ds  
    {

    }

  // Example expression to run {{{
  function expr1(): Expr
  {
    BinExpr(
      BinExpr(Var("x"), Times(), Var("y")),
        Plus(),
      BinExpr(BinExpr(Var("y"), Times(), Var("z")),
                Plus(),
              BinExpr(Var("x"), Times(), Var("z"))))
  }

  function env1(): Env
  {
    (v: string) =>
      if v == "x" then 3
      else if v == "y" then 4
      else if v == "z" then 5
      else 0
  }

  function resEval1(): Value
  {
    eval(env1(), expr1())
  }

  function bytecodes1(): Bytecodes
  {
    compile(expr1())
  }

  function resCompile1(): Option<Stack>
  {
    run(bytecodes1(), env1(), [])
  }
  // }}}


  // // Running compiled code gives same result as interpreting
  lemma correct(en: Env, expr: Expr, bs: Bytecodes, inStack: Stack)
    ensures run(compile(expr) + bs, en, inStack) == run(bs, en, push(eval(en, expr), inStack))
    {
      match expr {
        case ConstExpr(c) => 
        case Var(str) => 
        case BinExpr(left, b, right) =>
          var op := [BinOp(b)];
          var vLeft := eval(en, left);
          var vRight := eval(en, right);
          var midStack := push(vLeft, inStack);
          calc {
            run(compile(expr) + bs, en, inStack);
            == {assert compile(expr) == compile(left) + compile(right) + op; assoc4(compile(left), compile(right), op, bs); }
            run((compile(left) + (compile(right) + op)) + bs, en, inStack);
            == {assoc4(compile(left), compile(right), op, bs); 
                assert (compile(left) + (compile(right) + op)) + bs == compile(left) + (compile(right) + (op + bs));}
            run(compile(left) + (compile(right) + (op + bs)), en, inStack);
            == {correct(en, left, compile(right) + (op + bs), inStack);}
            run(compile(right) + (op + bs), en, midStack);
            == {correct(en, right, op + bs, midStack);}
            run(op + bs, en, push(vRight, midStack));
            == { 
              var stack: Stack := push(vRight, midStack);
              assert op == [BinOp(b)]; 
              assert vLeft == eval(en, left); 
              assert vRight == eval(en, right); 
              assert push(vRight, midStack) == [vRight] + [vLeft] + inStack;
              assert push(vRight, midStack) == stack;
              assert |stack| >= 2;
              assert |op + bs| > 0;
              var v1 := stack[0];
              var v2 := stack[1];
              var stack1 := stack[2..];
              var res := apply(b, v2, v1);
              assert res == apply(b, vLeft, vRight);
              assert run(op + bs, en, stack) == run(bs, en, push(res, stack1));
              }
            run(bs, en, push(apply(b, vLeft, vRight), inStack));
            == 
            run(bs, en, push(eval(en, expr), inStack));
            }
      }
    }
  
}