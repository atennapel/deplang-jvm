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

    case Pi(name: Bind, icit: Icit, ty: Ty, u1: Ty, body: Ty, u2: Ty)
    case Lam(name: Bind, icit: Icit, body: Tm)
    case App(fn: Tm, arg: Tm, icit: Icit)

    case Sigma(name: Bind, ty: Ty, u1: Ty, body: Ty, u2: Ty)
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

    case Meta(id: MetaId)
    case InsertedMeta(id: MetaId, bds: BDs)

    override def toString: String = this match
      case Local(x)  => s"'$x"
      case Global(x) => s"$x"
      case Let(x, App(U0, VFVal, Expl), t, v, b) =>
        s"(let $x : $t ::= $v in $b)"
      case Let(x, App(U0, VFFun, Expl), t, v, b) =>
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

      case Pi(DontBind, Expl, t, u1, b, u2)  => s"($t ->{$u1}{$u2} $b)"
      case Pi(DoBind(x), Expl, t, u1, b, u2) => s"(($x : $t) ->{$u1}{$u2} $b)"
      case Pi(x, Impl, t, u1, b, u2)         => s"({$x : $t} ->{$u1}{$u2} $b)"
      case Lam(x, Expl, b)                   => s"(\\$x. $b)"
      case Lam(x, Impl, b)                   => s"(\\{$x}. $b)"
      case App(f, a, Expl)                   => s"($f $a)"
      case App(f, a, Impl)                   => s"($f {$a})"

      case Sigma(DontBind, t, u1, b, u2)  => s"($t **{$u1}{$u2} $b)"
      case Sigma(DoBind(x), t, u1, b, u2) => s"(($x : $t) **{$u1}{$u2} $b)"
      case Pair(fst, snd)                 => s"($fst, $snd)"
      case Fst(t)                         => s"(fst $t)"
      case Snd(t)                         => s"(snd $t)"

      case Lift(_, t) => s"^$t"
      case Quote(t)   => s"`$t"
      case Splice(t)  => s"$$$t"

      case Wk(t) => s"(Wk $t)"

      case Nat        => "Nat"
      case Z          => "Z"
      case S(n)       => s"(S $n)"
      case FoldNat(t) => s"(foldNat {$t})"

      case Meta(id)            => s"?$id"
      case InsertedMeta(id, _) => s"?$id"
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
      case DDef(x, App(U0, VFVal, Expl), t, v) => s"$x : $t ::= $v"
      case DDef(x, App(U0, VFFun, Expl), t, v) => s"$x : $t := $v"
      case DDef(x, U1, t, v)                   => s"$x : $t = $v"
      case DDef(x, _, t, v)                    => s"$x : $t ?= $v"
  export Def.*
