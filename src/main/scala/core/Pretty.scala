package core

import common.Common.*
import Syntax.*

object Pretty:
  private def prettyPi(tm: Tm)(implicit ns: List[Name]): String = tm match
    case Pi(DontBind, t, _, b) =>
      s"${prettyParen(t, true)} -> ${prettyPi(b)(DontBind.toName :: ns)}"
    case Pi(DoBind(x0), t, _, b) =>
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
    case Local(_)          => pretty(tm)
    case Global(_)         => pretty(tm)
    case Type(S1)          => pretty(tm)
    case Type(S0(RVal))    => pretty(tm)
    case App(_, _) if app  => pretty(tm)
    case S(_) if app       => pretty(tm)
    case S(_)              => toNat(tm).fold(s"(${pretty(tm)})")(n => s"$n")
    case Lift(_, _)        => pretty(tm)
    case Quote(_)          => pretty(tm)
    case Splice(_)         => pretty(tm)
    case Nat               => pretty(tm)
    case Z                 => pretty(tm)
    case FoldNat(t) if app => pretty(tm)
    case PairTy(_, _)      => pretty(tm)
    case Pair(_, _)        => pretty(tm)
    case Fst(_)            => pretty(tm)
    case Snd(_)            => pretty(tm)
    case Wk(t)             => prettyParen(t, app)(ns.tail)
    case _                 => s"(${pretty(tm)})"

  def pretty(tm: Tm)(implicit ns: List[Name]): String = tm match
    case Local(ix) => s"${ns(ix.expose)}"
    case Global(x) => s"$x"
    case Let(x0, s, t, v, b) =>
      val x = x0.fresh
      s"let $x : ${pretty(t)} ${s
          .split(_ => ":", "")}= ${pretty(v)} in ${pretty(b)(x :: ns)}"

    case Type(S1)          => "Type1"
    case Type(S0(RVal))    => "Type"
    case Type(S0(RFun))    => "Type Fun"
    case Type(S0(RErased)) => "Type Erased"

    case Pi(_, _, _, _) => prettyPi(tm)
    case Lam(_, _)      => prettyLam(tm)
    case App(_, _)      => prettyApp(tm)

    case PairTy(fst, snd) => s"($fst ** $snd)"
    case Pair(fst, snd)   => s"($fst, $snd)"
    case Fst(t)           => s"(fst $t)"
    case Snd(t)           => s"(snd $t)"

    case Lift(_, t) => s"^${prettyParen(t)}"
    case Quote(t)   => s"`${prettyParen(t)}"
    case Splice(t)  => s"$$${prettyParen(t)}"

    case Wk(t) => pretty(t)(ns.tail)

    case Nat        => "Nat"
    case Z          => prettyNat(tm)
    case S(_)       => prettyNat(tm)
    case FoldNat(t) => s"foldNat {${pretty(t)}}"

  def pretty(d: Def)(implicit ns: List[Name]): String = d match
    case DDef(x0, s, t, v) =>
      val x = x0.fresh
      s"$x : ${pretty(t)} ${s.split(_ => ":", "")}= ${pretty(v)(x :: ns)};"

  def pretty(ds: Defs)(implicit ns: List[Name]): String =
    ds.toList.map(pretty).mkString("\n")
