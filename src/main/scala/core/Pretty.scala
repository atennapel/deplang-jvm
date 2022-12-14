package core

import common.Common.*
import Syntax.*

object Pretty:
  private def prettyPi(tm: Tm)(implicit ns: List[Name]): String = tm match
    case Pi(DontBind, Expl, t, _, b, _) =>
      s"${prettyParen(t, true)} -> ${prettyPi(b)(DontBind.toName :: ns)}"
    case Pi(DoBind(x0), Expl, t, _, b, _) =>
      val x = x0.fresh
      s"($x : ${pretty(t)}) -> ${prettyPi(b)(x :: ns)}"
    case Pi(x0, Impl, t, _, b, _) =>
      val x = x0.fresh
      s"{$x : ${pretty(t)}} -> ${prettyPi(b)(x.toName :: ns)}"
    case rest => pretty(rest)

  private def prettySigma(tm: Tm)(implicit ns: List[Name]): String = tm match
    case Sigma(DontBind, t, _, b, _) =>
      s"${prettyParen(t, true)} ** ${prettySigma(b)(DontBind.toName :: ns)}"
    case Sigma(DoBind(x0), t, _, b, _) =>
      val x = x0.fresh
      s"($x : ${pretty(t)}) ** ${prettySigma(b)(x :: ns)}"
    case rest => pretty(rest)

  private def prettyLam(tm: Tm)(implicit ns: List[Name]): String =
    def go(tm: Tm, ns: List[Name], first: Boolean = false): String = tm match
      case Lam(x0, Expl, b) =>
        val x = x0.fresh
        s"${if first then "" else " "}$x${go(b, x.toName :: ns)}"
      case Lam(x0, Impl, b) =>
        val x = x0.fresh
        s"${if first then "" else " "}{$x}${go(b, x.toName :: ns)}"
      case rest => s". ${pretty(rest)(ns)}"
    s"\\${go(tm, ns, true)}"

  private def prettyApp(tm: Tm)(implicit ns: List[Name]): String = tm match
    case App(f, a, Expl) => s"${prettyApp(f)} ${prettyParen(a)}"
    case App(f, a, Impl) => s"${prettyApp(f)} {${pretty(a)}}"
    case f               => prettyParen(f)

  private def toNat(tm: Tm): Option[Int] = tm match
    case Z    => Some(0)
    case S(n) => toNat(n).map(_ + 1)
    case _    => None

  private def prettyNat(tm: Tm)(implicit ns: List[Name]): String =
    def goPretty(tm: Tm): String = tm match
      case Z    => "Z"
      case S(n) => s"S ${prettyParen(n)}"
      case t    => pretty(t)
    toNat(tm).fold(goPretty(tm))(_.toString)

  private def prettyParen(tm: Tm, app: Boolean = false)(implicit
      ns: List[Name]
  ): String = tm match
    case Local(_)            => pretty(tm)
    case Global(_)           => pretty(tm)
    case VF                  => pretty(tm)
    case VFVal               => pretty(tm)
    case VFFun               => pretty(tm)
    case U0                  => pretty(tm)
    case U1                  => pretty(tm)
    case App(_, _, _) if app => pretty(tm)
    case S(_) if app         => pretty(tm)
    case S(_)                => toNat(tm).fold(s"(${pretty(tm)})")(n => s"$n")
    case Lift(_, _)          => pretty(tm)
    case Quote(_)            => pretty(tm)
    case Splice(_)           => pretty(tm)
    case Nat                 => pretty(tm)
    case Z                   => pretty(tm)
    case FoldNat(t) if app   => pretty(tm)
    case Pair(_, _)          => pretty(tm)
    case Fst(_)              => pretty(tm)
    case Snd(_)              => pretty(tm)
    case Meta(_)             => pretty(tm)
    case InsertedMeta(_, _)  => pretty(tm)
    case Wk(t)               => prettyParen(t, app)(ns.tail)
    case _                   => s"(${pretty(tm)})"

  def pretty(tm: Tm)(implicit ns: List[Name]): String = tm match
    case Local(ix) => s"${ns(ix.expose)}"
    case Global(x) => s"$x"
    case Let(x0, u, t, v, b) =>
      val x = x0.fresh
      val s = u match
        case App(U0, VFVal, Expl) => "::"
        case App(U0, VFFun, Expl) => ":"
        case U1                   => ""
        case _                    => "?"
      s"let $x : ${pretty(t)} $s= ${pretty(v)} in ${pretty(b)(x :: ns)}"

    case VF    => "VF"
    case VFVal => "Val"
    case VFFun => "Fun"
    case U0    => "U0"
    case U1    => "U1"

    case Pi(_, _, _, _, _, _) => prettyPi(tm)
    case Lam(_, _, _)         => prettyLam(tm)
    case App(_, _, _)         => prettyApp(tm)

    case Sigma(_, _, _, _, _) => prettySigma(tm)
    case Pair(fst, snd)       => s"($fst, $snd)"
    case Fst(t)               => s"(fst $t)"
    case Snd(t)               => s"(snd $t)"

    case Lift(_, t) => s"^${prettyParen(t)}"
    case Quote(t)   => s"`${prettyParen(t)}"
    case Splice(t)  => s"$$${prettyParen(t)}"

    case Wk(t) => pretty(t)(ns.tail)

    case Nat        => "Nat"
    case Z          => prettyNat(tm)
    case S(_)       => prettyNat(tm)
    case FoldNat(t) => s"foldNat {${pretty(t)}}"

    case Meta(id)            => s"?$id"
    case InsertedMeta(id, _) => s"?$id"

  def pretty(d: Def)(implicit ns: List[Name]): String = d match
    case DDef(x0, u, t, v) =>
      val x = x0.fresh
      val s = u match
        case App(U0, VFVal, Expl) => "::"
        case App(U0, VFFun, Expl) => ":"
        case U1                   => ""
        case _                    => "?"
      s"$x : ${pretty(t)} $s= ${pretty(v)(x :: ns)};"

  def pretty(ds: Defs)(implicit ns: List[Name]): String =
    ds.toList.map(pretty).mkString("\n")
