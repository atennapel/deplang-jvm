package core

import common.Common.*

object Syntax:
  type Ty = Tm
  enum Tm:
    case Local(ix: Ix)
    case Global(name: Name)
    case Let(name: Name, stage: Stage, ty: Ty, value: Tm, body: Tm)

    case Type(stage: Stage)

    case Pi(name: Bind, ty: Ty, stage: Stage, body: Ty)
    case Lam(name: Bind, body: Tm)
    case App(fn: Tm, arg: Tm)

    case PairTy(fst: Ty, snd: Ty)
    case Pair(fst: Tm, snd: Tm)
    case Fst(tm: Tm)
    case Snd(tm: Tm)

    case Lift(rep: Rep, tm: Ty)
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
      case Let(x, s, t, v, b) =>
        s"(let $x : $t ${s.split(_ => ":", "")}= $v in $b)"

      case Type(S1)       => s"Type1"
      case Type(S0(RVal)) => s"Type"
      case Type(S0(rep))  => s"(Type $rep)"

      case Pi(DontBind, t, _, b)  => s"($t -> $b)"
      case Pi(DoBind(x), t, _, b) => s"(($x : $t) -> $b)"
      case Lam(x, b)              => s"(\\$x. $b)"
      case App(f, a)              => s"($f $a)"

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
    case DDef(name: Name, stage: Stage, ty: Ty, value: Tm)

    override def toString: String = this match
      case DDef(x, s, t, v) => s"$x : $t ${s.split(_ => ":", "")}= $v;"
  export Def.*
