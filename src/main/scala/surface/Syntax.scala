package surface

import common.Common.*

object Syntax:
  type Ty = Tm
  enum Tm:
    case Var(name: Name)
    case Let(name: Name, univ: Ty, ty: Option[Ty], value: Tm, body: Tm)

    case Pi(name: Bind, icit: Icit, ty: Ty, body: Ty)
    case Lam(name: Bind, icit: Icit, body: Tm)
    case App(fn: Tm, arg: Tm, icit: Icit)

    case Sigma(name: Bind, ty: Ty, body: Ty)
    case Pair(fst: Tm, snd: Tm)

    case Lift(tm: Ty)
    case Quote(tm: Tm)
    case Splice(tm: Tm)

    case Hole(name: Option[Name])

    case Pos(pos: PosInfo, tm: Tm)

    override def toString: String = this match
      case Var(x) => s"$x"
      case Let(x, u, Some(t), v, b) =>
        val s = u.removePos match
          case App(Var(Name("U0")), Var(Name("Val")), Expl) => s"::"
          case App(Var(Name("U0")), Var(Name("Fun")), Expl) => s":"
          case Var(Name("U1"))                              => s""
          case _                                            => s"?"
        s"(let $x : $t $s= $v in $b)"
      case Let(x, u, None, v, b) =>
        val s = u.removePos match
          case App(Var(Name("U0")), Var(Name("Val")), Expl) => s"::"
          case App(Var(Name("U0")), Var(Name("Fun")), Expl) => s":"
          case Var(Name("U1"))                              => s""
          case _                                            => s"?"
        s"(let $x $s= $v in $b)"

      case Pi(DontBind, Expl, t, b)  => s"($t -> $b)"
      case Pi(DoBind(x), Expl, t, b) => s"(($x : $t) -> $b)"
      case Pi(x, Impl, t, b)         => s"({$x : $t} -> $b)"
      case Lam(x, Expl, b)           => s"(\\$x. $b)"
      case Lam(x, Impl, b)           => s"(\\{$x}. $b)"
      case App(f, a, Expl)           => s"($f $a)"
      case App(f, a, Impl)           => s"($f {$a})"

      case Lift(t)   => s"^$t"
      case Quote(t)  => s"`$t"
      case Splice(t) => s"$$$t"

      case Sigma(DontBind, t, b)  => s"($t ** $b)"
      case Sigma(DoBind(x), t, b) => s"(($x : $t) ** $b)"
      case Pair(fst, snd)         => s"($fst, $snd)"

      case Hole(Some(x)) => s"_$x"
      case Hole(None)    => "_"

      case Pos(_, t) => s"$t"

    def isPos: Boolean = this match
      case Pos(_, t) => true
      case _         => false

    def removePos: Tm = this match
      case Let(x, s, t, v, b) =>
        Let(x, s, t.map(_.removePos), v.removePos, b.removePos)

      case Pi(x, i, t, b) => Pi(x, i, t.removePos, b.removePos)
      case Lam(x, i, b)   => Lam(x, i, b.removePos)
      case App(f, a, i)   => App(f.removePos, a.removePos, i)

      case Lift(t)   => Lift(t.removePos)
      case Quote(t)  => Quote(t.removePos)
      case Splice(t) => Splice(t.removePos)

      case Sigma(x, t, b) => Sigma(x, t.removePos, b.removePos)
      case Pair(fst, snd) => Pair(fst.removePos, snd.removePos)

      case Pos(_, t) => t

      case _ => this
  export Tm.*

  final case class Defs(defs: List[Def]):
    override def toString: String = defs.mkString("\n")

    def toList: List[Def] = defs

  enum Def:
    case DDef(name: Name, univ: Ty, ty: Option[Ty], value: Tm)

    override def toString: String = this match
      case DDef(x, u, Some(t), v) =>
        val s = u.removePos match
          case App(Var(Name("U0")), Var(Name("Val")), Expl) => s"::"
          case App(Var(Name("U0")), Var(Name("Fun")), Expl) => s":"
          case Var(Name("U1"))                              => s""
          case _                                            => s"?"
        s"$x : $t $summon= $v;"
      case DDef(x, u, None, v) =>
        val s = u.removePos match
          case App(Var(Name("U0")), Var(Name("Val")), Expl) => s"::"
          case App(Var(Name("U0")), Var(Name("Fun")), Expl) => s":"
          case Var(Name("U1"))                              => s""
          case _                                            => s"?"
        s"$x $s= $v;"
  export Def.*
