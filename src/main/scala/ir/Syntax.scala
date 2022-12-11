package ir

import common.Common.*

object Syntax:
  enum Ty:
    case TNat

    override def toString: String = this match
      case TNat => "Nat"
  export Ty.*

  final case class TFun(left: Ty, right: Either[Ty, TFun]):
    override def toString: String =
      s"($left -> ${right.fold(_.toString, _.toString)})"

  enum Tm:
    case Local(ix: Ix)
    case Global(name: Name)
    case Let(name: Name, ty: Either[Ty, TFun], value: Tm, body: Tm)

    case Lam(name: Bind, body: Tm)
    case App(fn: Tm, arg: Tm)

    case Nat
    case Z
    case S(n: Tm)
    case FoldNat(ty: Ty)

    override def toString: String = this match
      case Local(x)  => s"'$x"
      case Global(x) => s"$x"
      case Let(x, t, v, b) =>
        s"(let $x : $t = $v in $b)"

      case Lam(x, b) => s"(\\$x. $b)"
      case App(f, a) => s"($f $a)"

      case Nat        => "Nat"
      case Z          => "Z"
      case S(n)       => s"(S $n)"
      case FoldNat(t) => s"(foldNat {$t})"
  export Tm.*

  final case class Defs(defs: List[Def]):
    override def toString: String = defs.mkString("\n")

    def toList: List[Def] = defs

  enum Def:
    case DDef(name: Name, ty: Either[Ty, TFun], value: Tm)

    override def toString: String = this match
      case DDef(x, Left(t), v)  => s"$x : $t = $v;"
      case DDef(x, Right(t), v) => s"$x : $t = $v;"
  export Def.*
