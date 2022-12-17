package ir

import Syntax.*

import scala.annotation.tailrec

/*
1. beta reduction: ((\x. t) u) ~> let x = u in t
2. inlining (let var is used once)
3. dead code removal (let var is not used)
4. (let f = \x. ... in t) u ~> let f = \x ... in t u
 */
object Simplifier:
  private val LIMIT = 100

  def simplify(ds: Defs): Defs = Defs(ds.toList.map(go))

  private def go(d: Def): Def = d match
    case DDef(x, t, v) => DDef(x, t, go(v, LIMIT)(Set.empty))

  @tailrec
  private def go(t: Tm, n: Int)(implicit scope: Set[Int]): Tm =
    if n > 0 then
      go(t) match
        case None     => t
        case Some(t2) => go(t2, n - 1)
    else t

  private def go(t: Tm)(implicit scope: Set[Int]): Option[Tm] = t match
    case Local(x, t)  => None
    case Global(x, t) => None

    case Let(x, t, v, b) =>
      val c = b.freeVars.count((y, _) => x == y)
      if c == 0 then Some(b)
      else if c == 1 then Some(b.subst(Map(x -> v), scope))
      else go2(v, b).map((v, b) => Let(x, t, v, b))

    case Lam(x, t1, t2, b) => go(b)(scope + x).map(b => Lam(x, t1, t2, b))

    case App(Let(x, t, v, b), a) =>
      if scope.contains(x) then
        val y = scope.max + 1
        Some(Let(y, t, v, App(b.subst(Map(x -> Local(y, t)), scope), a)))
      else Some(Let(x, t, v, App(b, a)))
    case App(Lam(x, t1, t2, b), a) => Some(Let(x, TDef(t1), a, b))
    case App(App(App(FoldNat(t), n), z), s) if n.toInt.isDefined =>
      var m = n.toInt.get
      var c: Tm = z
      var k: Tm = Z
      while (m > 0) do
        m -= 1
        c = App(App(s, k), c)
        k = S(k)
      Some(c)
    case App(f, a) => go2(f, a).map(App.apply)

    case Pair(t1, t2, fst, snd)     => go2(fst, snd).map(Pair(t1, t2, _, _))
    case Fst(_, Pair(_, _, fst, _)) => Some(fst)
    case Snd(_, Pair(_, _, _, snd)) => Some(snd)
    case Fst(ty, t)                 => go(t).map(Fst(ty, _))
    case Snd(ty, t)                 => go(t).map(Snd(ty, _))

    case Z          => None
    case S(n)       => go(n).map(S.apply)
    case FoldNat(t) => None

    case True  => None
    case False => None

    case If(t, True, a, b)  => Some(a)
    case If(t, False, a, b) => Some(b)

    // lift lambdas out
    case If(TDef(ps, rt), c, a, b) if ps.nonEmpty =>
      val (vs, innerscope) =
        ps.foldLeft[(List[(Int, Ty)], Set[Int])]((Nil, scope)) {
          case ((vs, scope), ty) =>
            val x = fresh(scope)
            (vs ++ List((x, ty)), scope + x)
        }
      val spine = vs.map((x, t) => Local(x, TDef(t)))
      val ea = a.apps(spine)
      val eb = b.apps(spine)
      Some(If(TDef(rt), c, ea, eb).lams(vs, rt))

    case If(t, c, a, b) =>
      go(c) match
        case Some(c) =>
          go2(a, b) match
            case Some((a, b)) => Some(If(t, c, a, b))
            case None         => Some(If(t, c, a, b))
        case None => go2(a, b).map(If(t, c, _, _))

  private def go2(a: Tm, b: Tm)(implicit scope: Set[Int]): Option[(Tm, Tm)] =
    (go(a), go(b)) match
      case (None, None)       => None
      case (Some(a), None)    => Some((a, b))
      case (None, Some(b))    => Some((a, b))
      case (Some(a), Some(b)) => Some((a, b))

  private def fresh(implicit scope: Set[Int]): Int =
    if scope.isEmpty then 0 else scope.max + 1
