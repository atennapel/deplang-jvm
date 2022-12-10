package core

import common.Common.*
import Syntax.*

object Pretty:
  private def prettyPi(tm: Tm)(implicit ns: List[Name]): String = tm match
    case Pi(DontBind, t, b) =>
      s"${prettyParen(t, true)} -> ${prettyPi(b)(DontBind.toName :: ns)}"
    case Pi(DoBind(x0), t, b) =>
      val x = x0.fresh
      s"($x : ${pretty(t)}) -> ${prettyPi(b)(x :: ns)}"
    case rest => pretty(rest)

  private def prettyLam(tm: Tm)(implicit ns: List[Name]): String =
    def go(tm: Tm, ns: List[Name], first: Boolean = false): String = tm match
      case Lam(x0, b) =>
        val x = x0.fresh
        s"${if first then "" else " "}$x${go(b, x.toName :: ns)}"
      case rest => s". ${pretty(rest)(ns)}"
    s"\\${go(tm, ns, true)}"

  private def prettyApp(tm: Tm)(implicit ns: List[Name]): String = tm match
    case App(f, a) => s"${prettyApp(f)} ${prettyParen(a)}"
    case f         => prettyParen(f)

  private def prettyParen(tm: Tm, app: Boolean = false)(implicit
      ns: List[Name]
  ): String = tm match
    case Local(_)         => pretty(tm)
    case Global(_)        => pretty(tm)
    case Type             => pretty(tm)
    case App(_, _) if app => pretty(tm)
    case _                => s"(${pretty(tm)})"

  def pretty(tm: Tm)(implicit ns: List[Name]): String = tm match
    case Local(ix) => s"${ns(ix.expose)}"
    case Global(x) => s"$x"
    case Let(x0, t, v, b) =>
      val x = x0.fresh
      s"let $x : ${pretty(t)} = ${pretty(v)} in ${pretty(b)(x :: ns)}"

    case Type => "Type"

    case Pi(_, _, _) => prettyPi(tm)
    case Lam(_, _)   => prettyLam(tm)
    case App(_, _)   => prettyApp(tm)

  def pretty(d: Def)(implicit ns: List[Name]): String = d match
    case DDef(x0, t, v) =>
      val x = x0.fresh
      s"$x : ${pretty(t)} = ${pretty(v)(x :: ns)};"

  def pretty(ds: Defs)(implicit ns: List[Name]): String =
    ds.toList.map(pretty).mkString("\n")
