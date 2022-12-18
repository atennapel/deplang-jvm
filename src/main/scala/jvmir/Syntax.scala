package jvmir

import common.Common.*

object Syntax:
  enum Ty:
    case TNat
    case TBool
    case TInt
    case TPair

    override def toString: String = this match
      case TNat  => "Nat"
      case TBool => "Bool"
      case TInt  => "Int"
      case TPair => s"Pair"
  export Ty.*

  final case class TDef(params: List[Ty], retrn: Ty):
    override def toString: String = params match
      case Nil => retrn.toString
      case ps  => s"(${ps.mkString(" -> ")} -> $retrn)"
  object TDef:
    def apply(t: Ty): TDef = TDef(Nil, t)

  enum Tm:
    case Arg(ix: Int, ty: Ty)
    case Local(name: Int, ty: Ty)
    case Global(name: Name, ty: TDef, args: List[Tm])
    case Let(name: Int, ty: Ty, value: Tm, body: Tm)

    case Pair(fst: Tm, snd: Tm)
    case Fst(tm: Tm)
    case Snd(tm: Tm)

    case Z
    case S(n: Tm)
    case FoldNat(ty: Ty, n: Tm, z: Tm, x1: Int, x2: Int, s: Tm)

    case True
    case False
    case If(ty: Ty, cond: Tm, ifTrue: Tm, ifFalse: Tm)

    case IntLit(value: Int)

    case Box(ty: Ty, tm: Tm)
    case Unbox(ty: Ty, tm: Tm)

    override def toString: String = this match
      case Arg(ix, _)        => s"'arg$ix"
      case Local(x, _)       => s"'$x"
      case Global(x, _, Nil) => s"$x"
      case Global(x, _, as)  => s"$x(${as.mkString(", ")})"
      case Let(x, t, v, b) =>
        s"(let '$x : $t = $v in $b)"

      case Pair(fst, snd) => s"($fst, $snd)"
      case Fst(t)         => s"(fst $t)"
      case Snd(t)         => s"(snd $t)"

      case Z    => "Z"
      case S(n) => s"(S $n)"
      case FoldNat(t, n, z, x1, x2, s) =>
        s"(foldNat {$t} $n $z ('$x1 '$x2. $s))"

      case True           => "True"
      case False          => "False"
      case If(_, c, a, b) => s"(if $c then $a else $b)"

      case IntLit(n) => s"$n"

      case Box(ty, tm)   => s"(box {$ty} $tm)"
      case Unbox(ty, tm) => s"(unbox {$ty} $tm)"

    def toInt: Option[Int] = this match
      case Z    => Some(0)
      case S(n) => n.toInt.map(_ + 1)
      case _    => None
  export Tm.*

  final case class Defs(defs: List[Def]):
    override def toString: String = defs.mkString("\n")

    def toList: List[Def] = defs

  enum Def:
    case DDef(
        name: Name,
        generated: Boolean,
        params: List[Ty],
        retrn: Ty,
        value: Tm
    )

    override def toString: String = this match
      case DDef(x, g, Nil, rt, v) =>
        s"${if g then "(gen) " else ""}$x : $rt = $v;"
      case DDef(x, g, ps, rt, v) =>
        s"${if g then "(gen) " else ""}$x (${ps.mkString(", ")}) : $rt = $v;"
  export Def.*
