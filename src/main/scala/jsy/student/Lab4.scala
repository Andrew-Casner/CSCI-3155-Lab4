package jsy.student

import jsy.lab4.Lab4Like
import sun.nio.cs.ext.Big5_HKSCS_2001

object Lab4 extends jsy.util.JsyApplication with Lab4Like {
  import jsy.lab4.ast._
  import jsy.lab4.Parser
  
  /*
   * CSCI 3155: Lab 4
   * <Your Name>
   * 
   * Partner: <Your Partner's Name>
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
    case Nil | _ :: Nil         => l
    case h1 :: (t1 @ (h2 :: _)) => if (h1==h2) compressRec(t1) else h1 :: compressRec(t1)
  }
  
  def compressFold[A](l: List[A]): List[A] = l.foldRight(Nil: List[A]){
    (h, acc)     => acc match {
      case h1::_ => if(h1==h) acc else h:: acc
      case _     => h::acc
    }
  }
  
  def mapFirst[A](l: List[A])(f: A => Option[A]): List[A] = l match {
    case Nil        => Nil
    case h :: t     => f(h) match {
      case  Some(a) => a::t
      case _        => h::mapFirst(t) (f)
    }
  }
  
  /* Trees */

  def foldLeft[A](t: Tree)(z: A)(f: (A, Int) => A): A = {
    def loop(acc: A, t: Tree): A = t match {
      case Empty         => acc
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
      (acc, x)             => acc match {
        case (b1, None)    => (b1, Some(x))
        case (b1, Some(e)) => if(e<x) (b1, Some(e)) else (false, Some(e))
      }
    }
    b
  }

  /* Type Inference */

  // While this helper function is completely given, this function is
  // worth studying to see how library methods are used.
  def hasFunctionTyp(t: Typ): Boolean = t match {
    case TFunction(_, _) => true
    case TObj(fields) if fields exists {
      case (_, t)        => hasFunctionTyp(t)
    }                    => true
    case _               => false
  }
  
  def typeof(env: TEnv, e: Expr): Typ = {
    def err[T](tgot: Typ, e1: Expr): T = throw StaticTypeError(tgot, e1, e)

    e match {
      case Print(e1)                       => typeof(env, e1); TUndefined
      case N(_)                            => TNumber
      case B(_)                            => TBool
      case Undefined                       => TUndefined
      case S(_)                            => TString
      case Var(x)                          => lookup(env, x)
      case Decl(mode, x, e1, e2)           => typeof(env+(x->typeof(env, e1)), e2)
      case Unary(Neg, e1)                  => typeof(env, e1) match {
        case TNumber                       => TNumber
        case tgot                          => err(tgot, e1)
      }
      case Unary(Not, e1)                  => typeof(env, e1) match {
        case TBool                         => TBool
        case tgot                          => err(tgot, e1)
      }
      case Binary(Plus, e1, e2)            => (typeof(env, e1), typeof(env, e2)) match {
          case (TString, TString)          => TString
          case (TNumber, TNumber)          => TNumber
          case (tgot, _)                   => err(tgot, e1)
          case (_, tgot)                   => err(tgot, e2)
        }
      case Binary(Minus|Times|Div, e1, e2) => (typeof(env, e1), typeof(env, e2)) match {
          case (TNumber, TNumber)          => TNumber
          case (tgot, _)                   => err(tgot, e1)
          case (_, tgot)                   => err(tgot, e2)
        }
      case Binary(Eq|Ne, e1, e2)           => (typeof(env, e1), typeof(env, e2)) match {
          case (TString, TString)          => TBool
          case (TNumber, TNumber)          => TBool
          case (tgot, _)                   => err(tgot, e1)
          case (_, tgot)                   => err(tgot, e2)
        }
      case Binary(Lt|Le|Gt|Ge, e1, e2)     => (typeof(env, e1), typeof(env, e2)) match {
          case (TString, TString)          => TBool
          case (TNumber, TNumber)          => TBool
          case (tgot, _)                   => err(tgot, e1)
          case (_, tgot)                   => err(tgot, e2)
        }
      case Binary(And|Or, e1, e2)          => (typeof(env, e1), typeof(env, e2)) match {
          case (TBool, TBool)              => TBool
          case (tgot, _)                   => err(tgot, e1)
          case (_, tgot)                   => err(tgot, e2)
        }
      case Binary(Seq, e1, e2)             => (typeof(env, e1), typeof(env, e2)) match {
          case (t1, t2)                    => t2
          case (tgot, _)                   => err(tgot, e1)
          case (_, tgot)                   => err(tgot, e2)
        }
      case If(e1, e2, e3)                  => (typeof(env, e1), typeof(env, e2), typeof(env, e3)) match {
          case  (TBool, e2, e3) if(e2==e3) => e2
          case (tgot, _, _)                => err(tgot, e1)
          case (_, tgot, _)                => err(tgot, e2)
          case (_, _, tgot)                => err(tgot, e3)
        }
      case Function(p, params, tann, e1)   => {
        // Bind to env1 an environment that extends env with an appropriate binding if
        // the function is potentially recursive.
        val env1 = (p, tann) match {
          case(None,_)                     => env
          case(Some(x),Some(t))            => extend(env,x,TFunction(params,t))
          case _                           => err(TUndefined, e1)
        }
        // Bind to env2 an environment that extends env1 with bindings for params.
        val env2 = params.foldLeft(env1){
          case(acc,(xi,MTyp(_,ti)))        => extend(acc,xi,ti)
        }
        // Infer the type of the function body
        val t1 = typeof(env2,e1)
        tann match{
          case(Some(t)) if(t1==t)          => TFunction(params,t)
          case(None)                       => TFunction(params,t1)
        }
      }
      case Call(e1, args)                  => typeof(env, e1) match {
        case TFunction(params, tret) if (params.length == args.length) =>
          val fPairs = params zip args
          fPairs.foreach {
            fPair =>
              val(v1,v2) = fPair
              if(v1._2.t != typeof(env,v2)) err(typeof(env,v2),v2)
          };
          tret
        case tgot => err(tgot, e1)
      }
      case Obj(fields)                       => TObj(fields mapValues( exp => typeof(env,exp)));
      case GetField(e1, f)                   => typeof(env,e1) match {
          case (TObj(fields))                => if(fields.contains(f)) fields(f) else throw StaticTypeError(typeof(env,e1),e1,e)
          case _                             => throw StaticTypeError(typeof(env,e1),e1,e)
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
      case (S(s1), S(s2)) => bop match {
        case Lt           => if(s1 < s2) true else false
        case Le           => if(s1 <= s2) true else false
        case Gt           => if(s1 > s2) true else false
        case Ge           => if(s1 >= s2) true else false
      }
      case (N(n1),N(n2))  => bop match {
        case Lt           => if(n1 < n2) true else false
        case Le           => if(n1 <= n2) true else false
        case Gt           => if(n1 > n2) true else false
        case Ge           => if(n1 >= n2) true else false
      }
    }
  }

  /* This should be the same code as from Lab 3 */
  def iterate(e0: Expr)(next: (Expr, Int) => Option[Expr]): Expr = {
    def loop(e: Expr, n: Int): Expr = next(e,n) match {
      case None => e
      case Some(e) => loop(e,n + 1)
    }
    loop(e0, 0)
  }

  /* Capture-avoiding substitution in e replacing variables x with esub. */
  def substitute(e: Expr, esub: Expr, x: String): Expr = {
    def subst(e: Expr): Expr = e match {
      case N(_) | B(_) | Undefined | S(_) => e
      case Print(e1)                      => Print(substitute(e1, esub, x))
      /***** Cases from Lab 3 */
      case Unary(uop, e1)                 => Unary(uop, subst(e1))
      case Binary(bop, e1, e2)            => Binary(bop, subst(e1), subst(e2))
      case If(e1, e2, e3)                 => If(subst(e1), subst(e2), subst(e3))
      case Var(y)                         => if(y==x) esub else e
      case Decl(mode, y, e1, e2)          =>  if (y == x) Decl(mode, y, subst(e1), e2) else Decl(mode, y, subst(e1),  subst(e2))
      /***** Cases needing adapting from Lab 3 */
      case Function(p, params, tann, e1)  =>
        if(params.exists((parameter: (String, MTyp)) => parameter._1 == x))
          Function(p, params, tann, e1)
        else
          Function(p, params, tann, subst(e1))
      case Call(e1, args)                 => Call(subst(e1), args.map{case (arg) => subst(arg)})
      /***** New cases for Lab 4 */
      case Obj(fields)                    => Obj(fields.mapValues(expr=> subst(expr)))
      case GetField(e1, f)                => GetField(subst(e1), f)
    }
    val fvs = freeVars(esub)
    def fresh(x: String): String = if (fvs.contains(x)) fresh(x + "$") else x
    subst(e)
  }

  /* Rename bound variables in e */
  def rename(e: Expr)(fresh: String => String): Expr = {
    def ren(env: Map[String,String], e: Expr): Expr = {
      e match {
        case N(_) | B(_) | Undefined | S(_) => e
        case Print(e1)                      => Print(ren(env, e1))

        case Unary(uop, e1)                 => Unary(uop, ren(env, e1))
        case Binary(bop, e1, e2)            => Binary(bop, ren(env, e1), ren(env, e2))
        case If(e1, e2, e3)                 => If(ren(env, e1), ren(env, e2), ren(env, e3))

        case Var(y)                         => if(env.contains(y)) Var(env(y)) else Var(y)
        case Decl(mode, y, e1, e2)          => Decl(mode, fresh(y), ren(env, e1), ren(env + (y -> fresh(y)), e2))
        case Function(p, params, retty, e1) => {
          val (pp, envp): (Option[String], Map[String,String]) = p match {
            case None                       => (None, env)
            case Some(x)                    => (Some(fresh(x)), extend(env, x, fresh(x)))
          }
          val (paramsp, envpp) = params.foldRight( (Nil: List[(String,MTyp)], envp) ) {
            case ((paramname, paramtype), (params, env)) => {
              val pfresh = fresh(paramname)
              ((pfresh, paramtype) :: params, extend(env, paramname, pfresh))
            }
          }
          Function(pp, paramsp, retty, ren(envpp, e1))
        }

        case Call(e1, args) => ???

        case Obj(fields) => ???
        case GetField(e1, f) => ???
      }
    }
    ren(empty, e)
  }

  /* Check whether or not an expression is reduced enough to be applied given a mode. */
  def isRedex(mode: Mode, e: Expr): Boolean = mode match {
    case MConst => !isValue(e)
    case MName => false
  }

  def step(e: Expr): Expr = {
    require(!isValue(e), s"step: e ${e} to step is a value")
    e match {
      /* Base Cases: Do Rules */
      case Print(v1) if isValue(v1)                           => println(pretty(v1)); Undefined
        /***** Cases needing adapting from Lab 3. */
      case Unary(Neg, v1) if isValue(v1)                      => v1 match {
        case N(n1)                                            => N(-n1)
        case _                                                => throw StuckError(e)
      }
      case Unary(Not, v1) if isValue(v1)                      => v1 match {
        case B(b1)                                            => B(!b1)
        case _                                                => throw StuckError(e)
      }
      case Binary(Seq, v1, e2) if isValue(v1)                 => e2
      case Binary(Plus, v1, v2) if isValue(v1) && isValue(v2) => (v1,v2) match {
        case (S(s1), S(s2))                                   => S(s1 + s2)
        case (N(n1), N(n2))                                   => N(n1+n2)
        case _                                                => throw StuckError(e)
      }
      case Binary(bop, v1, v2) if isValue(v1) && isValue(v2)  => (v1,v2) match {
        case (N(n1), N(n2))                                   => bop match {
          case Minus                                          => N(n1 + n2)
          case Div                                            => N(n1/n2)
          case Times                                          => N(n1*n2)
          case Lt | Le | Gt | Ge                              => B(inequalityVal(bop, v1, v2))
          case Eq                                             => B(v1 == v2)
          case Ne                                             => B(v1 != v2)
        }
        case _                                                => throw StuckError(e)
      }
      case Binary(And, v1, e2) if isValue(v1)                 => v1 match {
        case B(b)                                             => if(b) e2 else B(false)
        case _                                                => throw StuckError(e)
      }
      case Binary(Or, v1, e2) if isValue(v1)                  => v1 match {
        case B(b)                                             => if(b) B(true) else e2
        case _                                                => throw StuckError(e)
      }
      case If(v1, e2, e3) if isValue(v1)                      => v1 match {
        case B(b)                                             => if(b) e2 else e3
        case _                                                => throw StuckError(e)
      }
      case Decl(mode, x, e1, e2) if !isRedex(mode, e1)        => substitute(e2, e1, x)
      case GetField(v1, f) if isValue(v1)                     => v1 match {
        case Obj(fields)                                      => fields.get(f) match {
          case None                                           => throw StuckError(e)
          case Some(v)                                        => v
        }
        case _                                                => throw StuckError(e)
      }
      /***** More cases here */
      case Call(v1, args) if isValue(v1) =>
        v1 match {
          case Function(p, params, _, e1) => {
            val pazip = params zip args
            if (pazip.forall{ case((_, MTyp(m, _)), ei) => !isRedex(m, ei) }) {
              val e1p = pazip.foldRight(e1) {
                case (((x, _), argv), acc) => substitute(acc, argv, x)
              }
              p match {
                case None     => e1p
                case Some(x1) => ???
              }
            }
            else {
              val pazipp = mapFirst(pazip) {
                case (param@(_: String, MTyp(m, _)), arg: Expr) if isRedex(m, arg) => Some((param, step(arg)))
                case _                                                             => None
              }
              Call(v1, pazipp.unzip._2)
            }
          }
          case _ => throw StuckError(e)
        }
        /***** New cases for Lab 4. */

      /* Inductive Cases: Search Rules */
      case Print(e1)                            => Print(step(e1))
      /***** Cases from Lab 3. */
      case Unary(uop, e1)                       => Unary(uop, step(e1))
      case Binary(bop, e1, e2) if !isValue(e1)  => Binary(bop, step(e1) ,e2)
      case Binary(bop, v1, e2) if isValue(v1)   => Binary(bop, v1, step(e2))
      case If(e1, e2, e3)                       => If(step(e1) , e2, e3)
      case Decl(mode, x, e1, e2)                => Decl(mode, x, step(e1), e2)
        /***** More cases here */
        /***** Cases needing adapting from Lab 3 */
      case Obj(fields) if !isValue(e) => fields find {(f) => !isValue(f._2)} match { // finds first key that doesn't map to value
        case None          => throw StuckError(e) // we shouldn't reach this
        case Some((ff,e1)) => Obj(fields + (ff -> step(e1))) // update this key to map to stepped e
      }
      // search getfield
      case GetField(e1, f) => e1 match {
        case Obj(_)        => GetField(step(e1), f) // step object
        case _             => throw StuckError(e)
      }
      case Call(v1 @ Function(_, _, _, _), args) => ???
      case Call(e1, args) => ???
        /***** New cases for Lab 4. */

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

