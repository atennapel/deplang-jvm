package ir

import common.Common.*
import Syntax.*

import scala.annotation.tailrec

/*
1. beta reduction: ((\x. t) u) ~> let x = u in t
2. inlining (let var is used once)
3. dead code removal (let var is not used)
4. (let f = \x. ... in t) u ~> let f = \x ... in t u
5. lift lambdas out of eliminators and fix
 */
object Simplifier:
  private val LIMIT = 1000

  def simplify(ds: Defs): Defs = Defs(ds.toList.map(go))

  private def go(d: Def): Def = d match
    case DDef(x, t, v) => DDef(x, t, go(v, LIMIT)(Set.empty))
    case d             => d

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

    case Fix(g, x, t1, t2, b, arg) =>
      go(arg) match
        case Some(arg) =>
          go(b)(scope + g + x) match
            case Some(b) => Some(Fix(g, x, t1, t2, b, arg))
            case None    => Some(Fix(g, x, t1, t2, b, arg))
        case None => go(b)(scope + g + x).map(b => Fix(g, x, t1, t2, b, arg))

    case App(Let(x, t, v, b), a) =>
      if scope.contains(x) then
        val y = scope.max + 1
        Some(Let(y, t, v, App(b.subst(Map(x -> Local(y, t)), scope), a)))
      else Some(Let(x, t, v, App(b, a)))
    case App(Lam(x, t1, t2, b), a) => Some(Let(x, TDef(t1), a, b))
    case App(f, a)                 => go2(f, a).map(App.apply)

    case Pair(t1, t2, fst, snd)     => go2(fst, snd).map(Pair(t1, t2, _, _))
    case Fst(_, Pair(_, _, fst, _)) => Some(fst)
    case Snd(_, Pair(_, _, _, snd)) => Some(snd)
    case Fst(ty, t)                 => go(t).map(Fst(ty, _))
    case Snd(ty, t)                 => go(t).map(Snd(ty, _))

    case True  => None
    case False => None

    case IntLit(_) => None
    case Binop(op, a, b) =>
      binop(op, a, b) match
        case Some(t) => Some(t)
        case None    => go2(a, b).map(Binop(op, _, _))

    case NilL(_)          => None
    case ConsL(t, hd, tl) => go2(hd, tl).map(ConsL(t, _, _))

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
      Some(If(TDef(rt), c, ea, eb).lams(vs, TDef(rt)))

    case If(t, c, a, b) =>
      go(c) match
        case Some(c) =>
          go2(a, b) match
            case Some((a, b)) => Some(If(t, c, a, b))
            case None         => Some(If(t, c, a, b))
        case None => go2(a, b).map(If(t, c, _, _))

  private def binop(op: Op, a: Tm, b: Tm): Option[Tm] = (op, a, b) match
    case (OAdd, IntLit(a), IntLit(b)) => Some(IntLit(a + b))
    case (OAdd, IntLit(0), b)         => Some(b)
    case (OAdd, b, IntLit(0))         => Some(b)
    case (OMul, IntLit(a), IntLit(b)) => Some(IntLit(a * b))
    case (OMul, x, IntLit(1))         => Some(x)
    case (OMul, IntLit(1), x)         => Some(x)
    case (OMul, x, IntLit(0))         => Some(IntLit(0))
    case (OMul, IntLit(0), x)         => Some(IntLit(0))
    case (OSub, IntLit(a), IntLit(b)) => Some(IntLit(a - b))
    case (OSub, x, IntLit(0))         => Some(x)
    case (ODiv, IntLit(a), IntLit(b)) => Some(IntLit(a / b))
    case (ODiv, x, IntLit(1))         => Some(x)
    case (OMod, IntLit(a), IntLit(b)) => Some(IntLit(a % b))
    case (OEq, IntLit(a), IntLit(b))  => Some(if a == b then True else False)
    case (ONeq, IntLit(a), IntLit(b)) => Some(if a != b then True else False)
    case (OGt, IntLit(a), IntLit(b))  => Some(if a > b then True else False)
    case (OLt, IntLit(a), IntLit(b))  => Some(if a < b then True else False)
    case (OGeq, IntLit(a), IntLit(b)) => Some(if a >= b then True else False)
    case (OLeq, IntLit(a), IntLit(b)) => Some(if a <= b then True else False)
    case _                            => None

  private def go2(a: Tm, b: Tm)(implicit scope: Set[Int]): Option[(Tm, Tm)] =
    (go(a), go(b)) match
      case (None, None)       => None
      case (Some(a), None)    => Some((a, b))
      case (None, Some(b))    => Some((a, b))
      case (Some(a), Some(b)) => Some((a, b))

  def orL[A](f: A => Option[A], l: List[A]): Option[List[A]] =
    val l1 = l.map(x => (x, f(x)))
    if l1.forall((_, o) => o.isEmpty) then None
    else Some(l1.map((x, o) => o.getOrElse(x)))

  private def fresh(implicit scope: Set[Int]): Int =
    if scope.isEmpty then 0 else scope.max + 1
