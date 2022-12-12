package core

import common.Common.*

object Syntax:
  type Ty = Tm
  enum Tm:
    case Local(ix: Ix)
    case Global(name: Name)
    case Let(name: Name, univ: Ty, ty: Ty, value: Tm, body: Tm)

    case VF
    case VFVal
    case VFFun
    case U0
    case U1

    case Pi(name: Bind, ty: Ty, body: Ty)
    case Fun(left: Ty, vf: Ty, right: Ty)
    case Lam(name: Bind, body: Tm)
    case App(fn: Tm, arg: Tm)

    case PairTy(fst: Ty, snd: Ty)
    case Pair(fst: Tm, snd: Tm)
    case Fst(tm: Tm)
    case Snd(tm: Tm)

    case Lift(vf: Ty, tm: Ty)
    case Quote(tm: Tm)
    case Splice(tm: Tm)

    case Wk(tm: Tm)

    case Nat
    case Z
    case S(n: Tm)
    case FoldNat(ty: Ty)

    override def toString: String = this match
      case Local(x)  => s"'$x"
      case Global(x) => s"$x"
      case Let(x, App(U0, VFVal), t, v, b) =>
        s"(let $x : $t ::= $v in $b)"
      case Let(x, App(U0, VFFun), t, v, b) =>
        s"(let $x : $t := $v in $b)"
      case Let(x, U1, t, v, b) =>
        s"(let $x : $t = $v in $b)"
      case Let(x, _, t, v, b) =>
        s"(let $x : $t ?= $v in $b)"

      case VF    => s"VF"
      case VFVal => s"Val"
      case VFFun => s"Fun"
      case U0    => s"U0"
      case U1    => s"U1"

      case Pi(DontBind, t, b)  => s"($t -> $b)"
      case Pi(DoBind(x), t, b) => s"(($x : $t) -> $b)"
      case Fun(a, _, b)        => s"($a => $b)"
      case Lam(x, b)           => s"(\\$x. $b)"
      case App(f, a)           => s"($f $a)"

      case PairTy(fst, snd) => s"($fst ** $snd)"
      case Pair(fst, snd)   => s"($fst, $snd)"
      case Fst(t)           => s"(fst $t)"
      case Snd(t)           => s"(snd $t)"

      case Lift(_, t) => s"^$t"
      case Quote(t)   => s"`$t"
      case Splice(t)  => s"$$$t"

      case Wk(t) => s"(Wk $t)"

      case Nat        => "Nat"
      case Z          => "Z"
      case S(n)       => s"(S $n)"
      case FoldNat(t) => s"(foldNat {$t})"
  export Tm.*

  def tQuote(t: Tm): Tm = t match
    case Splice(t) => t
    case t         => Quote(t)
  def tSplice(t: Tm): Tm = t match
    case Quote(t) => t
    case t        => Splice(t)

  final case class Defs(defs: List[Def]):
    override def toString: String = defs.mkString("\n")

    def toList: List[Def] = defs

  enum Def:
    case DDef(name: Name, vf: Ty, ty: Ty, value: Tm)

    override def toString: String = this match
      case DDef(x, App(U0, VFVal), t, v) => s"$x : $t ::= $v"
      case DDef(x, App(U0, VFFun), t, v) => s"$x : $t := $v"
      case DDef(x, U1, t, v)             => s"$x : $t = $v"
      case DDef(x, _, t, v)              => s"$x : $t ?= $v"
  export Def.*
