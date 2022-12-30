package ir

import common.Common.*

object Syntax:
  enum Ty:
    case TBool
    case TInt
    case TPair(fst: Ty, snd: Ty)
    case TList(ty: Ty)

    override def toString: String = this match
      case TBool           => "Bool"
      case TInt            => "Int"
      case TPair(fst, snd) => s"($fst ** $snd)"
      case TList(t)        => s"(List $t)"
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
    case Fix(go: Int, name: Int, t1: Ty, t2: TDef, body: Tm, arg: Tm)
    case App(fn: Tm, arg: Tm)

    case Pair(t1: Ty, t2: Ty, fst: Tm, snd: Tm)
    case Fst(ty: Ty, tm: Tm)
    case Snd(ty: Ty, tm: Tm)

    case True
    case False
    case If(ty: TDef, cond: Tm, ifTrue: Tm, ifFalse: Tm)

    case IntLit(value: Int)
    case Binop(op: Op, left: Tm, right: Tm)

    case NilL(ty: Ty)
    case ConsL(ty: Ty, head: Tm, tail: Tm)
    case CaseL(
        scrut: Tm,
        ety: Ty,
        ty: TDef,
        nil: Tm,
        hd: Int,
        tl: Int,
        cons: Tm
    )

    override def toString: String = this match
      case Local(x, _)  => s"'$x"
      case Global(x, _) => s"$x"
      case Let(x, t, v, b) =>
        s"(let '$x : $t = $v in $b)"

      case Lam(x, _, _, b)          => s"(\\'$x. $b)"
      case Fix(go, x, _, _, b, arg) => s"(fix ('$go '$x. $b) $arg)"
      case App(f, a)                => s"($f $a)"

      case Pair(_, _, fst, snd) => s"($fst, $snd)"
      case Fst(_, t)            => s"(fst $t)"
      case Snd(_, t)            => s"(snd $t)"

      case True           => "True"
      case False          => "False"
      case If(_, c, a, b) => s"(if $c then $a else $b)"

      case IntLit(n)       => s"$n"
      case Binop(op, a, b) => s"($a $op $b)"

      case NilL(t)          => s"Nil"
      case ConsL(t, hd, tl) => s"(Cons $hd $tl)"
      case CaseL(s, _, _, nil, hd, tl, cons) =>
        s"(case $s $nil ($hd $tl. $cons))"

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
      case Fix(go, x, _, _, b, arg) =>
        b.freeVars.filterNot((y, _) => x == y || go == y) ++ arg.freeVars
      case App(f, a) => f.freeVars ++ a.freeVars

      case Pair(_, _, fst, snd) => fst.freeVars ++ snd.freeVars
      case Fst(_, t)            => t.freeVars
      case Snd(_, t)            => t.freeVars

      case If(_, c, a, b) => c.freeVars ++ a.freeVars ++ b.freeVars

      case Binop(_, a, b) => a.freeVars ++ b.freeVars

      case ConsL(_, hd, tl) => hd.freeVars ++ tl.freeVars
      case CaseL(s, _, _, nil, hd, tl, cons) =>
        s.freeVars ++ nil.freeVars ++ cons.freeVars.filterNot((y, _) =>
          y == hd || y == tl
        )

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

      case Fix(go, x, t1, t2, b, arg)
          if !scope.contains(go) && !scope.contains(x) =>
        Fix(
          go,
          x,
          t1,
          t2,
          b.subst(sub - go - x, scope + go + x),
          arg.subst(sub, scope)
        )
      case Fix(go, x, t1, t2, b, arg)
          if scope.contains(go) && !scope.contains(x) =>
        val go2 = scope.max + 1
        Fix(
          go2,
          x,
          t1,
          t2,
          b.subst(
            sub - x + (go -> Local(go2, TDef(t1, t2))),
            scope + x + go2
          ),
          arg.subst(sub, scope)
        )
      case Fix(go, x, t1, t2, b, arg)
          if !scope.contains(go) && scope.contains(x) =>
        val x2 = scope.max + 1
        Fix(
          go,
          x2,
          t1,
          t2,
          b.subst(
            sub - go + (x -> Local(x2, TDef(t1))),
            scope + x2 + go
          ),
          arg.subst(sub, scope)
        )
      case Fix(go, x, t1, t2, b, arg) =>
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
          ),
          arg.subst(sub, scope)
        )

      case Pair(t1, t2, fst, snd) =>
        Pair(t1, t2, fst.subst(sub, scope), snd.subst(sub, scope))
      case Fst(ty, tm) => Fst(ty, tm.subst(sub, scope))
      case Snd(ty, tm) => Snd(ty, tm.subst(sub, scope))

      case If(t, c, a, b) =>
        If(t, c.subst(sub, scope), a.subst(sub, scope), b.subst(sub, scope))

      case Binop(op, a, b) =>
        Binop(op, a.subst(sub, scope), b.subst(sub, scope))

      case ConsL(t, hd, tl) =>
        ConsL(t, hd.subst(sub, scope), tl.subst(sub, scope))

      case CaseL(s, et, t, nil, hd, tl, cons)
          if !scope.contains(hd) && !scope.contains(tl) =>
        CaseL(
          s.subst(sub, scope),
          et,
          t,
          nil.subst(sub, scope),
          hd,
          tl,
          cons.subst(sub - hd - tl, scope + hd + tl)
        )
      case CaseL(s, et, t, nil, hd, tl, cons)
          if scope.contains(hd) && !scope.contains(tl) =>
        val hd2 = scope.max + 1
        CaseL(
          s.subst(sub, scope),
          et,
          t,
          nil.subst(sub, scope),
          hd2,
          tl,
          cons.subst(
            sub - tl + (hd -> Local(hd2, TDef(et))),
            scope + hd2 + tl
          )
        )
      case CaseL(s, et, t, nil, hd, tl, cons)
          if !scope.contains(hd) && scope.contains(tl) =>
        val tl2 = scope.max + 1
        CaseL(
          s.subst(sub, scope),
          et,
          t,
          nil.subst(sub, scope),
          hd,
          tl2,
          cons.subst(
            sub - hd + (tl -> Local(
              tl2,
              TDef(TList(et))
            )),
            scope + hd + tl2
          )
        )
      case CaseL(s, et, t, nil, hd, tl, cons) =>
        val hd2 = scope.max + 1
        val tl2 = (scope + hd2).max + 1
        CaseL(
          s.subst(sub, scope),
          et,
          t,
          nil.subst(sub, scope),
          hd2,
          tl2,
          cons.subst(
            sub + (hd -> Local(hd2, TDef(et))) + (tl -> Local(
              tl2,
              TDef(TList(et))
            )),
            scope + hd2 + tl2
          )
        )

      case _ => this
  export Tm.*

  final case class Defs(defs: List[Def]):
    override def toString: String = defs.mkString("\n")

    def toList: List[Def] = defs

  enum Def:
    case DDef(name: Name, ty: TDef, value: Tm)

    override def toString: String = this match
      case DDef(x, t, v) => s"$x : $t = $v;"
  export Def.*
