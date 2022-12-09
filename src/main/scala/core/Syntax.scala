package core

import common.Common.*

object Syntax:
  type Ty = Tm
  enum Tm:
    case Local(ix: Ix)
    case Global(name: Name)
    case Let(name: Name, ty: Ty, value: Tm, body: Tm)

    case Type

    case Pi(name: Bind, ty: Ty, body: Ty)
    case Lam(name: Bind, body: Tm)
    case App(fn: Tm, arg: Tm)

    override def toString: String = this match
      case Local(x)        => s"$x"
      case Global(x)       => s"$x"
      case Let(x, t, v, b) => s"(let $x : $t = $v in $b)"

      case Type => "Type"

      case Pi(DontBind, t, b)  => s"($t -> $b)"
      case Pi(DoBind(x), t, b) => s"(($x : $t) -> $b)"
      case Lam(x, b)           => s"(\\$x. $b)"
      case App(f, a)           => s"($f $a)"
  export Tm.*

  final case class Defs(defs: List[Def]):
    override def toString: String = defs.mkString("\n")

    def toList: List[Def] = defs

  enum Def:
    case DDef(name: Name, ty: Ty, value: Tm)

    override def toString: String = this match
      case DDef(x, t, v) => s"$x : $t = $v;"
  export Def.*
