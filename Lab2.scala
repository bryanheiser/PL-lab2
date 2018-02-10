package jsy.student

import jsy.lab2.Lab2Like

object Lab2 extends jsy.util.JsyApplication with Lab2Like {
  import jsy.lab2.Parser
  import jsy.lab2.ast._

  /*
   * CSCI 3155: Lab 2
   * <Bryan Heiser>
   * 
   * Partner: <Luke Nguyen>
   * Collaborators: <Any Collaborators>
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   * 
   * Replace the '???' expression with  your code in each function.
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
   * '???' as needed to get something  that compiles without error. The '???'
   * is a Scala expression that throws the exception scala.NotImplementedError.
   *
   */

  /* We represent a variable environment as a map from a string of the
   * variable name to the value to which it is bound.
   * 
   * You may use the following provided helper functions to manipulate
   * environments, which are just thin wrappers around the Map type
   * in the Scala standard library.  You can use the Scala standard
   * library directly, but these are the only interfaces that you
   * need.
   */



  /* Some useful Scala methods for working with Scala values include:
   * - Double.NaN
   * - s.toDouble (for s: String)
   * - n.isNaN (for n: Double)
   * - n.isWhole (for n: Double)
   * - s (for n: Double)
   * - s format n (for s: String [a format string like for printf], n: Double)
   *
   * You can catch an exception in Scala using:
   * try ... catch { case ... => ... }
   */

  def toNumber(v: Expr): Double = {
    require(isValue(v))
    (v: @unchecked) match {
      case N(n) => n
      case B(b) => if (b) 1 else 0
      case S(s) =>
        val number = s.toDouble
        if (number.isNaN) throw new IllegalArgumentException("String must not contain alphabetical characters") else number
      case _ => Double.NaN
    }
  }

  def toBoolean(v: Expr): Boolean = {
    require(isValue(v))
    (v: @unchecked) match {
      case B(b) => b
      case N(n) => if (n==0) false else true
      case S(s) => s match {
        case "" => false
        case _ => true
      }
      case _ => throw new IllegalArgumentException("Cannot be converted to Type Boolean")
    }
  }

  def toStr(v: Expr): String = {
    require(isValue(v))
    (v: @unchecked) match {
      case S(s) => s
      case B(b) => if (b) "true" else "false"
      case N(n) => n.toString
      case Undefined => "undefined"
      case _ => throw new IllegalArgumentException("Cannot be converted to Type String")
    }
  }

  def eval(env: Env, e: Expr): Expr = {
    e match {
      /* Base Cases */
      case N(_) | S(_) | B(_) | Undefined => e
      case Var(x) => lookup(env, x)

      /* Inductive Cases */
      case Print(e1) => println(pretty(eval(env, e1))); Undefined

      case ConstDecl(x, e1, e2) => {
        val p:Expr = eval(env, e1)
        val env1:Env = env + (x -> p)
        eval(env1, e2)
      }

      case If(e1, e2, e3) => eval(env, e1) match {
        case B(b) => if (b) eval(env, e2) else eval(env, e3)
        case _ => throw new IllegalArgumentException("First expression does not evaluate to Boolean")
      }

      case Unary(uop, e1) => uop match {
        case Neg => eval(env, e1) match {
          case N(n) => N(-n)
          case B(b) => if (b) N(-1) else N(-0)
          case _ => N(Double.NaN)
        }
        case Not => eval(env, e1) match {
          case N(n) => if (n==0) B(true) else B(false)
          case B(b) => if (b) B(false) else B(true)
          case S(s) => B(false)
          case Undefined => B(true)
        }
      }

      case Binary(bop, e1, e2) => bop match {
        case Plus => (eval(env, e1), eval(env,e2)) match {
          case (N(n1), N(n2)) => N(n1 + n2)
          case (S(s), uk) => S(s + toStr(uk))
          case (uk, S(s)) => S(toStr(uk) + s)
          case (S(s1), S(s2)) => S(s1 + s2)
          case (v1,v2) => N(toNumber(v1) + toNumber(v2))
        }
        case Minus => (eval(env, e1), eval(env, e2)) match {
          case (N(n1), N(n2)) => N(n1 - n2)
          case (S(s), uk) => N(Double.NaN)
          case (uk, S(s)) => N(Double.NaN)
          case (S(s1), S(s2)) => N(Double.NaN)
          case (v1, v2) => N(toNumber(v1) - toNumber(v2))
        }
        case Times => (eval(env, e1), eval(env, e2)) match {
          case (N(n1), N(n2)) => N(n1 * n2)
          case (S(s), uk) => N(Double.NaN)
          case (uk, S(s)) => N(Double.NaN)
          case (S(s1), S(s2)) => N(Double.NaN)
          case (v1, v2) => N(toNumber(v1) * toNumber(v2))
        }
        case Div => (eval(env, e1), eval(env, e2)) match {
          case (N(n1), N(n2)) => N(n1 / n2)
          case (S(s), uk) => N(Double.NaN)
          case (uk, S(s)) => N(Double.NaN)
          case (S(s1), S(s2)) => N(Double.NaN)
          case (v1, v2) => N(toNumber(v1) / toNumber(v2))
        }
        case Eq => (eval(env, e1), eval(env, e2)) match {
          case (N(n1), N(n2)) => if (n1==n2) B(true) else B(false)
          case (S(s1), S(s2)) => if (s1==s2) B(true) else B(false)
          case (B(b1), B(b2)) => if (b1==b2) B(true) else B(false)
          case (v1, v2) => B(false)
        }
        case Ne => (eval(env, e1), eval(env, e2)) match {
          case (N(n1), N(n2)) => if (n1==n2) B(false) else B(true)
          case (S(s1), S(s2)) => if (s1==s2) B(false) else B(true)
          case (B(b1), B(b2)) => if (b1==b2) B(false) else B(true)
          case (v1, v2) => B(true)
        }
        case Lt => (eval(env, e1), eval(env, e2)) match {
          case (N(n1), N(n2)) => if (n1 < n2) B(true) else B(false)
          case (S(s1), S(s2)) => if (s1 < s2) B(true) else B(false)
          case (S(s), uk) => B(false)
          case (uk, S(s)) => B(false)
          case (B(b1), B(b2)) => if (b1 < b2) B(true) else B(false)
          case (v1, v2) => if (toNumber(v1) < toNumber(v2)) B(true) else B(false)
        }
        case Le => (eval(env, e1), eval(env, e2)) match {
          case (N(n1), N(n2)) => if (n1 <= n2) B(true) else B(false)
          case (S(s1), S(s2)) => if (s1 <= s2) B(true) else B(false)
          case (S(s), uk) => B(false)
          case (uk, S(s)) => B(false)
          case (B(b1), B(b2)) => if (b1 <= b2) B(true) else B(false)
          case (v1, v2) => if (toNumber(v1) <= toNumber(v2)) B(true) else B(false)
        }
        case Gt => (eval(env, e1), eval(env, e2)) match {
          case (N(n1), N(n2)) => if (n1 > n2) B(true) else B(false)
          case (S(s1), S(s2)) => if (s1 > s2) B(true) else B(false)
          case (S(s), uk) => B(false)
          case (uk, S(s)) => B(false)
          case (B(b1), B(b2)) => if (b1 > b2) B(true) else B(false)
          case (v1, v2) => if (toNumber(v1) > toNumber(v2)) B(true) else B(false)
        }
        case Ge => (eval(env, e1), eval(env, e2)) match {
          case (N(n1), N(n2)) => if (n1 >= n2) B(true) else B(false)
          case (S(s1), S(s2)) => if (s1 >= s2) B(true) else B(false)
          case (S(s), uk) => B(false)
          case (uk, S(s)) => B(false)
          case (B(b1), B(b2)) => if (b1 >= b2) B(true) else B(false)
          case (v1, v2) => if (toNumber(v1) >= toNumber(v2)) B(true) else B(false)
        }
        case And => (eval(env, e1), eval(env, e2)) match {
          case (N(n1), N(n2)) => if (n1!=0 && n2!=0) N(n2) else N(0)
          case (N(n), uk) => if (n!=0) uk else N(0)
          case (B(b), uk) => if (b) uk else B(false)
          case (_, B(b)) => if (b) B(true) else B(false)
          case (S(s1), S(s2)) => S(s2)
        }
        case Or => (eval(env, e1), eval(env, e2)) match {
          case (B(false), B(false)) => B(false)
          case (N(0), N(0)) => N(0)
          case (B(true), B(true)) | (_, B(true)) | (B(true), _) => B(true)
          case (uk, _) => uk
        }
        case Seq => eval(env, e1); eval(env, e2)
      }

      case _ => Undefined 
    }
  }



  /* Interface to run your interpreter from the command-line.  You can ignore what's below. */
  def processFile(file: java.io.File) {
    if (debug) { println("Parsing ...") }

    val expr = Parser.parseFile(file)

    if (debug) {
      println("\nExpression AST:\n  " + expr)
      println("------------------------------------------------------------")
    }

    if (debug) { println("Evaluating ...") }

    val v = eval(expr)

     println(pretty(v))
  }

}
