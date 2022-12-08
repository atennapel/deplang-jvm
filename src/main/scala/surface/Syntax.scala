package surface

import common.Common.*

object Syntax:
  type Ty = Tm
  enum Tm:
    case Var(name: Name)
    case Let(name: Name, ty: Ty, value: Tm, body: Tm)

    case Type

    case Pi(name: Bind, ty: Ty, body: Ty)
    case Lam(name: Bind, body: Tm)
    case App(fn: Tm, arg: Tm)

    case Hole(name: Option[Name])

    case Pos(pos: PosInfo, tm: Tm)

    override def toString: String = this match
      case Var(x)          => s"$x"
      case Let(x, t, v, b) => s"(let $x : $t = $v in $b)"

      case Type => "Type"

      case Pi(DontBind, t, b)  => s"($t -> $b)"
      case Pi(DoBind(x), t, b) => s"(($x : $t) -> $b)"
      case Lam(x, b)           => s"(\\$x. $b)"
      case App(f, a)           => s"($f $a)"

      case Hole(Some(x)) => s"_$x"
      case Hole(None)    => "_"

      case Pos(_, t) => s"$t"
  export Tm.*

  final case class Defs(defs: List[Def]):
    override def toString: String = defs.mkString("\n")

    def toList: List[Def] = defs

  enum Def:
    case DDef(name: Name, ty: Ty, value: Tm)

    override def toString: String = this match
      case DDef(x, t, v) => s"def $x : $t = $v;"
  export Def.*
