package core

import common.Common.*

object Syntax:
  enum ProjType:
    case Fst
    case Snd
    case Named(name: Option[Name], ix: Int)

    override def toString: String = this match
      case Fst               => ".1"
      case Snd               => ".2"
      case Named(Some(x), _) => s".$x"
      case Named(None, i)    => s".$i"
  export ProjType.*

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
    case Fix(go: Name, name: Name, body: Tm)

    case Sigma(name: Bind, ty: Ty, u1: Ty, body: Ty, u2: Ty)
    case Proj(tm: Tm, proj: ProjType)
    case Pair(fst: Tm, snd: Tm)

    case Lift(vf: Ty, tm: Ty)
    case Quote(tm: Tm)
    case Splice(tm: Tm)

    case Wk(tm: Tm)

    case Nat
    case Z
    case S(n: Tm)
    case FoldNat(ty: Ty)

    case Bool
    case True
    case False
    case If(ty: Ty, cond: Tm, ifTrue: Tm, ifFalse: Tm)

    case IntTy
    case IntLit(value: Int)
    case Binop(op: Op, left: Tm, right: Tm)

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
      case Fix(go, x, b)                     => s"(fix $go $x. $b)"

      case Sigma(DontBind, t, u1, b, u2)  => s"($t **{$u1}{$u2} $b)"
      case Sigma(DoBind(x), t, u1, b, u2) => s"(($x : $t) **{$u1}{$u2} $b)"
      case Pair(fst, snd)                 => s"($fst, $snd)"
      case Proj(tm, proj)                 => s"$tm$proj"

      case Lift(_, t) => s"^$t"
      case Quote(t)   => s"`$t"
      case Splice(t)  => s"$$$t"

      case Wk(t) => s"(Wk $t)"

      case Nat        => "Nat"
      case Z          => "Z"
      case S(n)       => s"(S $n)"
      case FoldNat(t) => s"(foldNat {$t})"

      case Bool           => "Bool"
      case True           => "True"
      case False          => "False"
      case If(_, c, a, b) => s"(if $c then $a else $b)"

      case IntTy           => "Int"
      case IntLit(v)       => s"$v"
      case Binop(op, a, b) => s"($a $op $b)"

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
