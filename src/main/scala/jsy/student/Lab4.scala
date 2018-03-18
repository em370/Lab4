package jsy.student

import jsy.lab4.Lab4Like

object Lab4 extends jsy.util.JsyApplication with Lab4Like {
  import jsy.lab4.ast._
  import jsy.lab4.Parser
  
  /*
   * CSCI 3155: Lab 4
   * <Eric Minor>
   *
   * Partner: <Gordon Gu>
   * Collaborators: <Any Collaborators>
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   * 
   * Replace the '???' expression with your code in each function.
   *
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your Lab object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   *
   * Your lab will not be graded if it does not compile.
   *
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert. Simply put in a
   * '???' as needed to get something that compiles without error. The '???'
   * is a Scala expression that throws the exception scala.NotImplementedError.
   */
  
  /* Collections and Higher-Order Functions */
  
  /* Lists */
  
  def compressRec[A](l: List[A]): List[A] = l match {
    case Nil | _ :: Nil => l
    case h1 :: (t1 @ (h2 :: _)) => if(h1!=h2) h1::compressRec(t1) else compressRec(t1)
  }
  
  def compressFold[A](l: List[A]): List[A] = l.foldRight(Nil: List[A]){
    (h, acc) => acc match{
      case Nil => h::acc
      case h1::_ => if(h!=h1) h::acc else acc
    }
  }
  
  def mapFirst[A](l: List[A])(f: A => Option[A]): List[A] = l match {
    case Nil => Nil
    case h :: t => f(h) match {
      case Some(a) => a::t
      case None => h::mapFirst(t)(f)
    }
  }
  
  /* Trees */

  def foldLeft[A](t: Tree)(z: A)(f: (A, Int) => A): A = {
    def loop(acc: A, t: Tree): A = t match {
      case Empty => acc
      case Node(l, d, r) => loop(f(loop(acc,l),d),r)
    }
    loop(z, t)
  }

  // An example use of foldLeft
  def sum(t: Tree): Int = foldLeft(t)(0){ (acc, d) => acc + d }

  // Create a tree from a list. An example use of the
  // List.foldLeft method.
  def treeFromList(l: List[Int]): Tree =
    l.foldLeft(Empty: Tree){ (acc, i) => acc insert i }

  def strictlyOrdered(t: Tree): Boolean = {
    val (b, _) = foldLeft(t)((true, None: Option[Int])){
      (acc,d) => acc match {
        case (false,_) => (false, None)
        case (true, None) => (true,Some(d))
        case (true,Some(s)) => if(d>s) (true,Some(d)) else (false,None)
      }
    }
    b
  }

  /* Type Inference */

  // While this helper function is completely given, this function is
  // worth studying to see how library methods are used.
  def hasFunctionTyp(t: Typ): Boolean = t match {
    case TFunction(_, _) => true
    case TObj(fields) if (fields exists { case (_, t) => hasFunctionTyp(t) }) => true
    case _ => false
  }
  def getType(e:Expr): Typ = {
    typeof(empty,e)
  }
  def typeof(env: TEnv, e: Expr): Typ = {
    def err[T](tgot: Typ, e1: Expr): T = throw StaticTypeError(tgot, e1, e)

    e match {
      case Print(e1) => typeof(env, e1); TUndefined
      case N(_) => TNumber
      case B(_) => TBool
      case Undefined => TUndefined
      case S(_) => TString
      case Var(x) => if(env contains x) lookup(env, x) else err(TUndefined, e)
      case Decl(mode, x, e1, e2) => typeof(extend(env, x, typeof(env, e1)), e2)
      case Unary(Neg, e1) => typeof(env, e1) match {
        case TNumber => TNumber
        case tgot => err(tgot, e1)
      }
      case Unary(Not, e1) =>typeof(env, e1) match {
        case TBool => TBool
        case tgot => err(tgot, e1)
      }
      case Binary(Plus, e1, e2) => (typeof(env,e1), typeof(env,e2)) match {
        case (TNumber,TNumber) => TNumber
        case (TString,TString) => TString
        case (TNumber | TString, tgot) => err(tgot, e2)
        case (tgot, TString | TNumber) => err(tgot, e1)
        case (tgot,_) => err(tgot,e1)
      }
      case Binary(Minus|Times|Div, e1, e2) => (typeof(env,e1), typeof(env,e2)) match {
        case (TNumber,TNumber) => TNumber
        case (tgot, TNumber) => err(tgot, e1)
        case (TNumber, tgot) => err(tgot, e2)
        case (tgot,_) => err(tgot,e1)
      }
      case Binary(Eq|Ne, e1, e2) => (typeof(env,e1), typeof(env,e2)) match {
        case (t1, t2) => if (t1 == t2) TBool else err(t2, e2)
        case (t1, _) if hasFunctionTyp(t1) => err(t1, e1)
        case (_, t2) if hasFunctionTyp(t2) => err(t2, e2)
      }
      case Binary(Lt|Le|Gt|Ge, e1, e2) => (typeof(env,e1), typeof(env,e2)) match {
        case (TNumber,TNumber)|(TString,TString) => TBool
        case (tgot, TString|TNumber) => err(tgot, e1)
        case (TNumber|TString, tgot) => err(tgot, e2)
        case (tgot,_) => err(tgot,e1)
      }
      case Binary(And|Or, e1, e2) =>(typeof(env,e1), typeof(env,e2)) match {
        case (TBool,TBool) => TBool
        case (TBool, tgot) => err(tgot, e2)
        case (tgot,_) => err(tgot,e1)
      }
      case Binary(Seq, e1, e2) => (typeof(env,e1), typeof(env,e2)) match {
        case (_ , t2) => t2
      }
      case If(e1, e2, e3) => (typeof(env,e1),typeof(env,e2),typeof(env,e3)) match {
        case (TBool,t1,t2) if(t1==t2) => t1 else err(t2,e2)
        case (tgot,_,_) => err(tgot,e1)
      }
      case Function(p, params, tann, e1) => {
        // Bind to env1 an environment that extends env with an appropriate binding if
        // the function is potentially recursive.
        val env1 = (p, tann) match {
          /***** Add cases here *****/
          case ((Some(name), Some(ty)) => extend(env, name, TFunction(params, ty))
          case (None,_)=>env
          case _ => err(TUndefined, e1)
        }
        // Bind to env2 an environment that extends env1 with bindings for params.
        val env2 = params.foldLeft(env1:TEnv)({
          case (currEnv, (s: String, MTyp(_, t))) => extend(currEnv, s, t)
        })
        // Infer the type of the function body
        val t1 = typeof(env2,e1)
        // Check with the possibly annotated return type
        tann match{
          case Some(t2) => if(TFunction(params,t1) == TFunction(params,t2)) TFunction(params, t1) else err(TFunction(params, t2), e)
          case None => TFunction(params,t1)
        }
      }
      case Call(e1, args) => typeof(env, e1) match {
        case TFunction(params, tret) if (params.length == args.length) =>
          (params zip args).foreach {
            a => a match{
              case ((_,MTyp(_,pty: Typ)),arg) => if(pty != getType(arg)) err(getType(arg),e)
            }
          };
          tret
        case tgot => err(tgot, e1)
      }
      case Obj(fields) => {
        val fieldtypes = fields.foldLeft(Map(): Map[String,Typ]){
          (acc,d) => d match{
            case (name,e2:Expr) => extend(acc,name, getType(e2))
          }
        }
        TObj(fieldtypes)
      }
      case GetField(e1, f) => getType(e1) match{
        case TObj(types) => lookup(types,f)
        case othertype => err(othertype, e)
      }
    }
  }
  
  
  /* Small-Step Interpreter */

  /*
   * Helper function that implements the semantics of inequality
   * operators Lt, Le, Gt, and Ge on values.
   *
   * We suggest a refactoring of code from Lab 2 to be able to
   * use this helper function in eval and step.
   *
   * This should the same code as from Lab 3.
   */
  def inequalityVal(bop: Bop, v1: Expr, v2: Expr): Boolean = {
    require(isValue(v1), s"inequalityVal: v1 ${v1} is not a value")
    require(isValue(v2), s"inequalityVal: v2 ${v2} is not a value")
    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    (v1, v2) match {
      case (S(s1), S(s2)) => bop match { // must be string or number
        case Lt => s1<s2
        case Le => s1<=s2
        case Gt => s1>s2
        case Ge => s1>=s2
      }
      case (N(n1), N(n2)) => bop match {
        case Lt => n1 < n2
        case Le => n1 <= n2
        case Gt => n1 > n2
        case Ge => n1 >= n2
      }
    }
  }

  /* This should be the same code as from Lab 3 */
  def iterate(e0: Expr)(next: (Expr, Int) => Option[Expr]): Expr = {
    def loop(e: Expr, n: Int): Expr = next(e,n) match {
      case None => e
      case Some(exp) => loop(exp, n+1)
    }
    loop(e0, 0)
  }

  /* Capture-avoiding substitution in e replacing variables x with esub. */
  def substitute(e: Expr, esub: Expr, x: String): Expr = {
    def subst(e: Expr): Expr = e match {
      case N(_) | B(_) | Undefined | S(_) => e
      case Print(e1) => Print(substitute(e1, esub, x))
        /***** Cases from Lab 3 */
      case Unary(uop, e1) => Unary(uop,substitute(e1,esub,x))
      case Binary(bop, e1, e2) => Binary(bop, substitute(e1,esub,x),substitute(e2,esub,x))
      case If(e1, e2, e3) => If(substitute(e1,esub,x),substitute(e2,esub,x),substitute(e3,esub,x))
      case Var(y) => if (y==x) esub else Var(y)
      case Decl(mode, y, e1, e2) => if (y!=x) Decl(mode,y,substitute(e1,esub,x),substitute(e2,esub,x)) else Decl(mode,y,substitute(e1,esub,x),e2)
        /***** Cases needing adapting from Lab 3 */
      case Function(p, params, tann, e1) => p match {
        case Some(pp) => if (pp == x || params.exists(pa => pa._1 == x)) e else substitute(e1, esub, x)
        case None => if (params.exists(pa => pa._1 == x)) e else substitute(e1, esub, x)
      }
      case Call(e1, args) => Call(substitute(e1, esub, x), args map {
        (ei) => substitute(ei, esub, x)
      })
        /***** New cases for Lab 4 */
      case Obj(fields) => Obj(fields mapValues {
        (exp) => substitute(exp, esub, x)
      })
      case GetField(e1, f) => GetField(substitute(e1, esub, x), f)
    }

    val fvs = freeVars(esub)
    def fresh(x: String): String = if (fvs contains x) fresh(x + "$") else x
    subst(rename(e)(fresh))
  }

  /* Rename bound variables in e */
  def rename(e: Expr)(fresh: String => String): Expr = {
    def ren(env: Map[String,String], e: Expr): Expr = {
      e match {
        case N(_) | B(_) | Undefined | S(_) => e
        case Print(e1) => Print(ren(env, e1))

        case Unary(uop, e1) => Unary(uop, ren(env, e1))
        case Binary(bop, e1, e2) => Binary(bop, ren(env, e1), ren(env, e2))
        case If(e1, e2, e3) => If(ren(env ,e1), ren(env, e2), ren(env, e3))

        case Var(y) => if (env contains y) Var(lookup(env, y)) else Var(y)
        case Decl(mode, y, e1, e2) =>
          val yp = fresh(y)
          Decl(mode, yp, ren(env, e1), ren(extend(env, y, yp), e2))

        case Function(p, params, retty, e1) => {
          val (pp, envp): (Option[String], Map[String,String]) = p match {
            case None => (None, env)
            case Some(x) => val x2 = fresh(x); (Some(x2), env + (x -> x2))
          }
          val (paramsp, envpp) = params.foldRight( (Nil: List[(String,MTyp)], envp) ) {
            case ((s, mt @ MTyp(_,_)), (prevList , prevEnv)) => val s2 = fresh(s)
                  ((s2, mt) :: prevList, prevEnv + (s -> s2))
          }
          Function(pp, paramsp, retty, ren(envpp, e1))
        }

        case Call(e1, args) => Call(ren(env, e1), args map {
          case (ex) => ren(env, ex)
        })

        case Obj(fields) => Obj(fields mapValues((ex) => ren(env, ex)))
        case GetField(e1, f) => GetField(ren(env, e1), f)
      }
    }
    ren(empty, e)
  }

  /* Check whether or not an expression is reduced enough to be applied given a mode. */
  def isRedex(mode: Mode, e: Expr): Boolean = mode match {
    case MConst => if (! isValue(e)) true else false
    case MName => false
  }

  def step(e: Expr): Expr = {
    require(!isValue(e), s"step: e ${e} to step is a value")
    e match {
      /* Base Cases: Do Rules */
      case Print(v1) if isValue(v1) => println(pretty(v1)); Undefined
        /***** Cases needing adapting from Lab 3. */
      case Unary(Neg, N(n)) => N(-n)
      case Unary(Not, B(b)) => B(!b)
      case Binary(Seq,e1,e2) if isValue(e1) => e2
      case Binary(op@(Plus|Minus|Div|Times),N(n1),N(n2)) => op match {
        case Plus => N(n1+n2)
        case Minus => N(n1-n2)
        case Div => N(n1/n2)
        case Times => N(n1*n2)
      }
      case Binary(Plus,S(s1),S(s2)) => S(s1+s2)
      case Binary(op@(Gt|Lt|Ge|Le),e1@N(_),e2@N(_)) => B(inequalityVal(op,e1,e2))
      case Binary(op@(Gt|Lt|Ge|Le),e1@S(_),e2@S(_)) => B(inequalityVal(op,e1,e2))
      case Binary(op@(Eq|Ne),e1,e2) if(isValue(e1) && isValue(e2)) => op match{
        case Eq=> B(e1==e2)
        case Ne=> B(e1!=e2)
      }
      case Binary(And,B(true),e2) => e2
      case Binary(And,B(false),e2) => B(false)
      case Binary(Or,B(true),e2) => B(true)
      case Binary(Or,B(false),e2) => e2
      case If(B(true),e2,_) => e2
      case If(B(false),_,e3) => e3
      case Decl(mode, x, e1, e2) if !isRedex(mode, e1) => substitute(e2, e1, x)
        /***** More cases here */
      case Call(v1, args) if isValue(v1) =>
        v1 match {
          case Function(p, params, _, e1) => {
            val pazip = params zip args
            if (pazip forall { case ((_, MTyp(m,_)), arg) => !isRedex(m, arg) }) {
              val e1p = pazip.foldRight(e1) {
                case (((x, _), arg_param), acc) => substitute(acc, arg_param, x)
              }
              p match {
                case None => e1p
                case Some(x1) => substitute(e1p, v1, x1)
              }
            }
            else {
              val pazipp = mapFirst(pazip) { /** this is searchCall2 **/
                case (par@(_, MTyp(m,_)), arg) => if (isRedex(m,arg)) Some((par,step(arg))) else None
              }
              val (params,args2) = pazipp.unzip
              Call(v1,args2)
            }
          }
          case _ => throw StuckError(e)
        }
        /***** New cases for Lab 4. */
      case GetField(e1@Obj(f),s) if (f.toList forall { case (fname,fe) => isValue(fe) }) =>  lookup(f,s)
      /* Inductive Cases: Search Rules */
      case Print(e1) => Print(step(e1))
        /***** Cases from Lab 3. */
      case Unary(uop, e1) => Unary(uop,step(e1))
      case Binary(bop,e1,e2) => Binary(bop,step(e1),e1)
      case Binary(bop,v1,e2) if(isValue(v1)) => Binary(bop,v1,step(e2))
      case If(e1,e2,e3) => If(step(e1),e2,e3)
      case Decl(mode, x, e1, e2) => if isRedex(mode, e1) => Decl(mode, x, step(e1), e2)
      
        /***** More cases here */
      case Obj(fields) if ! isValue(e) => fields find {(f) => ! isValue(f._)} match {
        case None => throw StuckError(e)
        case Some((fx,e1)) => Obj(fields + (fx -> step(e1)))
      }
      
      case GetField(e1, f) => e1 match {
        case Obj(_) => GetField(step(e1), f)
        case _ => throw StuckError(e)
      }
      
        /***** Cases needing adapting from Lab 3 */
      /** Why is this here? case Call(v1 @ Function(p,params_, _, e1), args) => {

      }**/
      case Call(e1, args) => Call(step(e1),args)

        /***** New cases for Lab 4.*/

      /* Everything else is a stuck error. Should not happen if e is well-typed.
       *
       * Tip: you might want to first develop by comment out the following line to see which
       * cases you have missing. You then uncomment this line when you are sure all the cases
       * that you have left the ones that should be stuck.
       */
      case _ => throw StuckError(e)
    }
  }
  
  
  /* External Interfaces */
  
  //this.debug = true // uncomment this if you want to print debugging information
  this.keepGoing = true // comment this out if you want to stop at first exception when processing a file
}

