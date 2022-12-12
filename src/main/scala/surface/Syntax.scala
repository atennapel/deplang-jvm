package surface

import common.Common.*

object Syntax:
  type Ty = Tm
  enum Tm:
    case Var(name: Name)
    case Let(name: Name, univ: Ty, ty: Option[Ty], value: Tm, body: Tm)

    case Pi(name: Bind, ty: Ty, body: Ty)
    case Lam(name: Bind, body: Tm)
    case App(fn: Tm, arg: Tm)

    case PairTy(fst: Ty, snd: Ty)
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
          case App(Var(Name("U0")), Var(Name("Val"))) => s"::"
          case App(Var(Name("U0")), Var(Name("Fun"))) => s":"
          case Var(Name("U1"))                        => s""
          case _                                      => s"?"
        s"(let $x : $t $s= $v in $b)"
      case Let(x, u, None, v, b) =>
        val s = u.removePos match
          case App(Var(Name("U0")), Var(Name("Val"))) => s"::"
          case App(Var(Name("U0")), Var(Name("Fun"))) => s":"
          case Var(Name("U1"))                        => s""
          case _                                      => s"?"
        s"(let $x $s= $v in $b)"

      case Pi(DontBind, t, b)  => s"($t -> $b)"
      case Pi(DoBind(x), t, b) => s"(($x : $t) -> $b)"
      case Lam(x, b)           => s"(\\$x. $b)"
      case App(f, a)           => s"($f $a)"

      case Lift(t)   => s"^$t"
      case Quote(t)  => s"`$t"
      case Splice(t) => s"$$$t"

      case PairTy(fst, snd) => s"($fst ** $snd)"
      case Pair(fst, snd)   => s"($fst, $snd)"

      case Hole(Some(x)) => s"_$x"
      case Hole(None)    => "_"

      case Pos(_, t) => s"$t"

    def isPos: Boolean = this match
      case Pos(_, t) => true
      case _         => false

    def removePos: Tm = this match
      case Let(x, s, t, v, b) =>
        Let(x, s, t.map(_.removePos), v.removePos, b.removePos)

      case Pi(x, t, b) => Pi(x, t.removePos, b.removePos)
      case Lam(x, b)   => Lam(x, b.removePos)
      case App(f, a)   => App(f.removePos, a.removePos)

      case Lift(t)   => Lift(t.removePos)
      case Quote(t)  => Quote(t.removePos)
      case Splice(t) => Splice(t.removePos)

      case PairTy(fst, snd) => PairTy(fst.removePos, snd.removePos)
      case Pair(fst, snd)   => Pair(fst.removePos, snd.removePos)

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
          case App(Var(Name("U0")), Var(Name("Val"))) => s"::"
          case App(Var(Name("U0")), Var(Name("Fun"))) => s":"
          case Var(Name("U1"))                        => s""
          case _                                      => s"?"
        s"$x : $t $summon= $v;"
      case DDef(x, u, None, v) =>
        val s = u.removePos match
          case App(Var(Name("U0")), Var(Name("Val"))) => s"::"
          case App(Var(Name("U0")), Var(Name("Fun"))) => s":"
          case Var(Name("U1"))                        => s""
          case _                                      => s"?"
        s"$x $s= $v;"
  export Def.*
