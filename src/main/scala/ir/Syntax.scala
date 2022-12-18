package ir

import common.Common.*

object Syntax:
  enum Ty:
    case TNat
    case TBool
    case TInt
    case TPair(fst: Ty, snd: Ty)

    override def toString: String = this match
      case TNat            => "Nat"
      case TBool           => "Bool"
      case TInt            => "Int"
      case TPair(fst, snd) => s"($fst ** $snd)"
  export Ty.*

  final case class TDef(params: List[Ty], retrn: Ty):
    override def toString: String = params match
      case Nil => retrn.toString
      case ps  => s"(${ps.mkString(" -> ")} -> $retrn)"
  object TDef:
    def apply(t: Ty): TDef = TDef(Nil, t)
    def apply(t: Ty, rt: TDef): TDef = TDef(t :: rt.params, rt.retrn)

  enum Tm:
    case Local(name: Int, ty: TDef)
    case Global(name: Name, ty: TDef)
    case Let(name: Int, ty: TDef, value: Tm, body: Tm)

    case Lam(name: Int, t1: Ty, t2: TDef, body: Tm)
    case Fix(go: Int, name: Int, t1: Ty, t2: TDef, body: Tm)
    case App(fn: Tm, arg: Tm)

    case Pair(t1: Ty, t2: Ty, fst: Tm, snd: Tm)
    case Fst(ty: Ty, tm: Tm)
    case Snd(ty: Ty, tm: Tm)

    case Z
    case S(n: Tm)
    case FoldNat(ty: Ty)

    case True
    case False
    case If(ty: TDef, cond: Tm, ifTrue: Tm, ifFalse: Tm)

    case IntLit(value: Int)
    case Binop()

    override def toString: String = this match
      case Local(x, _)  => s"'$x"
      case Global(x, _) => s"$x"
      case Let(x, t, v, b) =>
        s"(let '$x : $t = $v in $b)"

      case Lam(x, _, _, b)     => s"(\\'$x. $b)"
      case Fix(go, x, _, _, b) => s"(fix '$go '$x. $b)"
      case App(f, a)           => s"($f $a)"

      case Pair(_, _, fst, snd) => s"($fst, $snd)"
      case Fst(_, t)            => s"(fst $t)"
      case Snd(_, t)            => s"(snd $t)"

      case Z          => "Z"
      case S(n)       => s"(S $n)"
      case FoldNat(t) => s"(foldNat {$t})"

      case True           => "True"
      case False          => "False"
      case If(_, c, a, b) => s"(if $c then $a else $b)"

      case IntLit(n) => s"$n"

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

    def lams(ps: List[(Int, Ty)], rt: TDef): Tm =
      ps.foldRight[(Tm, TDef)]((this, rt)) { case ((x, t), (b, rt)) =>
        (Lam(x, t, rt, b), TDef(t :: rt.params, rt.retrn))
      }._1

    def apps(args: List[Tm]) = args.foldLeft(this)(App.apply)

    def freeVars: List[(Int, TDef)] = this match
      case Local(x, t) => List((x, t))
      case Let(x, _, v, b) =>
        v.freeVars ++ b.freeVars.filterNot((y, _) => x == y)

      case Lam(x, _, _, b) => b.freeVars.filterNot((y, _) => x == y)
      case Fix(go, x, _, _, b) =>
        b.freeVars.filterNot((y, _) => x == y || go == y)
      case App(f, a) => f.freeVars ++ a.freeVars

      case Pair(_, _, fst, snd) => fst.freeVars ++ snd.freeVars
      case Fst(_, t)            => t.freeVars
      case Snd(_, t)            => t.freeVars

      case S(n) => n.freeVars

      case If(_, c, a, b) => c.freeVars ++ a.freeVars ++ b.freeVars

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

      case Fix(go, x, t1, t2, b) if !scope.contains(go) && !scope.contains(x) =>
        Fix(go, x, t1, t2, b.subst(sub - go - x, scope + go + x))
      case Fix(go, x, t1, t2, b) if scope.contains(go) && !scope.contains(x) =>
        val go2 = scope.max + 1
        Fix(
          go2,
          x,
          t1,
          t2,
          b.subst(
            sub + (go -> Local(go2, TDef(t1, t2))),
            scope + go2
          )
        )
      case Fix(go, x, t1, t2, b) if !scope.contains(go) && scope.contains(x) =>
        val x2 = scope.max + 1
        Fix(
          go,
          x2,
          t1,
          t2,
          b.subst(
            sub + (x -> Local(x2, TDef(t1))),
            scope + x2
          )
        )
      case Fix(go, x, t1, t2, b) =>
        val go2 = scope.max + 1
        val x2 = (scope + go2).max + 1
        Fix(
          go2,
          x2,
          t1,
          t2,
          b.subst(
            sub + (go -> Local(go2, TDef(t1, t2))) + (x -> Local(x2, TDef(t1))),
            scope + go2 + x2
          )
        )

      case Pair(t1, t2, fst, snd) =>
        Pair(t1, t2, fst.subst(sub, scope), snd.subst(sub, scope))
      case Fst(ty, tm) => Fst(ty, tm.subst(sub, scope))
      case Snd(ty, tm) => Snd(ty, tm.subst(sub, scope))

      case S(n: Tm) => S(n.subst(sub, scope))

      case If(t, c, a, b) =>
        If(t, c.subst(sub, scope), a.subst(sub, scope), b.subst(sub, scope))

      case _ => this

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
