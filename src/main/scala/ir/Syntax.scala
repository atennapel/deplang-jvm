package ir

import common.Common.*

object Syntax:
  enum Ty:
    case TNat
    case TPair(fst: Ty, snd: Ty)

    override def toString: String = this match
      case TNat            => "Nat"
      case TPair(fst, snd) => s"($fst ** $snd)"
  export Ty.*

  final case class TDef(params: List[Ty], retrn: Ty):
    override def toString: String = params match
      case Nil => retrn.toString
      case ps  => s"(${ps.mkString(" -> ")} -> $retrn)"
  object TDef:
    def apply(t: Ty): TDef = TDef(Nil, t)

  enum Tm:
    case Local(name: Int, ty: TDef)
    case Global(name: Name, ty: TDef)
    case Let(name: Int, ty: TDef, value: Tm, body: Tm)

    case Lam(name: Int, t1: Ty, t2: TDef, body: Tm)
    case App(fn: Tm, arg: Tm)

    case Pair(fst: Tm, snd: Tm)
    case Fst(tm: Tm)
    case Snd(tm: Tm)

    case Z
    case S(n: Tm)
    case FoldNat(ty: Ty)

    override def toString: String = this match
      case Local(x, _)  => s"'$x"
      case Global(x, _) => s"$x"
      case Let(x, t, v, b) =>
        s"(let '$x : $t = $v in $b)"

      case Lam(x, _, _, b) => s"(\\'$x. $b)"
      case App(f, a)       => s"($f $a)"

      case Pair(fst, snd) => s"($fst, $snd)"
      case Fst(t)         => s"(fst $t)"
      case Snd(t)         => s"(snd $t)"

      case Z          => "Z"
      case S(n)       => s"(S $n)"
      case FoldNat(t) => s"(foldNat {$t})"

    def flattenLams: (List[(Int, Ty)], Option[Ty], Tm) =
      def go(t: Tm): (List[(Int, Ty)], Option[Ty], Tm) = t match
        case Lam(x, t1, t2, b) =>
          val (xs, rt, b2) = go(b)
          ((x, t1) :: xs, rt.fold(Some(t2.retrn))(t => Some(t)), b2)
        case b => (Nil, None, b)
      go(this)

    def flattenApps: (Tm, List[Tm]) = this match
      case App(f, a) =>
        val (hd, as) = f.flattenApps
        (hd, as ++ List(a))
      case t => (t, Nil)

    def freeVars: List[(Int, TDef)] = this match
      case Local(x, t) => List((x, t))
      case Let(x, _, v, b) =>
        v.freeVars ++ b.freeVars.filterNot((y, _) => x == y)

      case Lam(x, _, _, b) => b.freeVars.filterNot((y, _) => x == y)
      case App(f, a)       => f.freeVars ++ a.freeVars

      case Pair(fst, snd) => fst.freeVars ++ snd.freeVars
      case Fst(t)         => t.freeVars
      case Snd(t)         => t.freeVars

      case S(n) => n.freeVars

      case _ => Nil

    def subst(sub: Map[Int, Tm]): Tm =
      subst(
        sub,
        sub.values
          .map(t => t.freeVars.map(_._1).toSet)
          .foldRight(Set.empty[Int])((a, b) => a ++ b)
      )
    def subst(sub: Map[Int, Tm], scope: Set[Int]): Tm = this match
      case Local(x, t)  => sub.get(x).getOrElse(this)
      case Global(x, t) => this
      case Let(x, t, v, b) if !scope.contains(x) =>
        Let(x, t, v.subst(sub, scope), b.subst(sub - x, scope + x))
      case Let(x, t, v, b) =>
        val y = scope.max + 1
        Let(y, t, v, b.subst(sub + (x -> Local(y, t)), scope + y))

      case Lam(x, t1, t2, b) if !scope.contains(x) =>
        Lam(x, t1, t2, b.subst(sub - x, scope + x))
      case Lam(x, t1, t2, b) =>
        val y = scope.max + 1
        Lam(y, t1, t2, b.subst(sub + (x -> Local(y, TDef(t1))), scope + y))
      case App(f, a) => App(f.subst(sub, scope), a.subst(sub, scope))

      case Pair(fst, snd) => Pair(fst.subst(sub, scope), snd.subst(sub, scope))
      case Fst(tm)        => Fst(tm.subst(sub, scope))
      case Snd(tm)        => Snd(tm.subst(sub, scope))

      case S(n: Tm) => S(n.subst(sub, scope))
      case _        => this

    def toInt: Option[Int] = this match
      case Z    => Some(0)
      case S(n) => n.toInt.map(_ + 1)
      case _    => None
  export Tm.*

  final case class Defs(defs: List[Def]):
    override def toString: String = defs.mkString("\n")

    def toList: List[Def] = defs

  enum Def:
    case DDef(name: Name, ty: TDef, value: Tm)

    override def toString: String = this match
      case DDef(x, t, v) => s"$x : $t = $v;"
  export Def.*
