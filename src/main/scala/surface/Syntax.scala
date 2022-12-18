package surface

import common.Common.*

object Syntax:
  enum ProjType:
    case Fst
    case Snd
    case Named(name: Name)

    override def toString: String = this match
      case Fst      => ".1"
      case Snd      => ".2"
      case Named(x) => s".$x"
  export ProjType.*

  type Ty = Tm
  enum Tm:
    case Var(name: Name)
    case Let(name: Name, univ: Ty, ty: Option[Ty], value: Tm, body: Tm)

    case Pi(name: Bind, icit: Icit, ty: Ty, body: Ty)
    case Lam(name: Bind, icit: Icit, body: Tm)
    case App(fn: Tm, arg: Tm, icit: Icit)
    case Fix(go: Name, name: Name, body: Tm)

    case Sigma(name: Bind, ty: Ty, body: Ty)
    case Proj(tm: Tm, proj: ProjType)
    case Pair(fst: Tm, snd: Tm)

    case Lift(tm: Ty)
    case Quote(tm: Tm)
    case Splice(tm: Tm)

    case If(cond: Tm, ifTrue: Tm, ifFalse: Tm)

    case IntLit(value: Int)

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
      case Fix(go, x, b)             => s"(fix $go $x. $b)"

      case Lift(t)   => s"^$t"
      case Quote(t)  => s"`$t"
      case Splice(t) => s"$$$t"

      case Sigma(DontBind, t, b)  => s"($t ** $b)"
      case Sigma(DoBind(x), t, b) => s"(($x : $t) ** $b)"
      case Proj(tm, proj)         => s"$tm$proj"
      case Pair(fst, snd)         => s"($fst, $snd)"

      case If(c, a, b) => s"(if $c then $a else $b)"

      case IntLit(n) => s"$n"

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
      case Fix(go, x, b)  => Fix(go, x, b.removePos)

      case Lift(t)   => Lift(t.removePos)
      case Quote(t)  => Quote(t.removePos)
      case Splice(t) => Splice(t.removePos)

      case Sigma(x, t, b) => Sigma(x, t.removePos, b.removePos)
      case Proj(t, p)     => Proj(t.removePos, p)
      case Pair(fst, snd) => Pair(fst.removePos, snd.removePos)

      case If(c, a, b) => If(c.removePos, a.removePos, b.removePos)

      case Pos(_, t) => t.removePos

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
