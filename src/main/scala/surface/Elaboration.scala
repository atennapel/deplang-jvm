package surface

import common.Common.*
import common.Debug.*
import core.Syntax.*
import core.Value.*
import core.Evaluation.*
import core.Unification.{unify as unify0, UnifyError}
import core.Globals.*
import core.Metas.*
import core.Zonking.*
import Ctx.*
import Syntax as S

import scala.annotation.tailrec

object Elaboration:
  final case class ElaborateError(msg: String) extends Exception(msg)

  private def newMeta()(implicit ctx: Ctx): Tm =
    InsertedMeta(freshMeta(), ctx.bds)

  private def insertPi(inp: (Ty, VTy, VTy))(implicit ctx: Ctx): (Ty, VTy, VTy) =
    def go(tm: Ty, ty: VTy, u: VTy): (Tm, VTy, VTy) = force(ty) match
      case VPi(x, Impl, a, u1, b, u2) =>
        val m = newMeta()
        val mv = ctx.eval(m)
        go(App(tm, m, Impl), b(mv), u2)
      case _ => (tm, ty, u)
    go(inp._1, inp._2, inp._3)

  private def insert(inp: (Tm, VTy, VTy))(implicit ctx: Ctx): (Tm, VTy, VTy) =
    inp._1 match
      case Lam(_, Impl, _) => inp
      case _               => insertPi(inp)

  private def unify(a: VTy, b: VTy)(implicit ctx: Ctx): Unit =
    try unify0(a, b)(ctx.lvl)
    catch
      case e: UnifyError =>
        throw ElaborateError(
          s"cannot unify: ${ctx.pretty(a)} ~ ${ctx.pretty(b)}: ${e.msg}"
        )

  private def inferValue(v: S.Tm, t: Option[S.Ty], u: VTy)(implicit
      ctx: Ctx
  ): (Tm, Ty, VTy) = t match
    case None =>
      val (etm, vty) = infer(v, u)
      (etm, ctx.quote(vty), vty)
    case Some(ty) =>
      val ety = checkType(ty, u)
      val vty = ctx.eval(ety)
      val etm = check(v, vty, u)
      (etm, ety, vty)

  private def checkType(t: S.Ty, u: VTy)(implicit ctx: Ctx): Ty =
    check(t, u, VU1)

  private def inferType(t: S.Ty)(implicit ctx: Ctx): (Ty, VTy, VTy) =
    val (et, vt, u) = infer(t)
    force(vt) match
      case VU1    => (et, vt, u)
      case VU(vf) => (et, vt, u)
      case _ =>
        throw ElaborateError(s"expected type for $t, but got ${ctx.pretty(vt)}")

  private def tryAdjustStage(t: Tm, a: VTy, st1: VTy, st2: VTy)(implicit
      ctx: Ctx
  ): Option[(Tm, VTy)] =
    debug(
      s"tryAdjustStage ${ctx.pretty(t)} : ${ctx.pretty(a)} from ${ctx
          .pretty(st1)} to ${ctx.pretty(st2)}"
    )
    (force(st1), force(st2)) match
      case (v1, v2) if v1 == v2 => None
      case (VU(vf), VU1)        => Some(tQuote(t), VLift(vf, a))
      case (VU1, VU(vf)) =>
        force(a) match
          case VLift(vf2, a) if vf == vf2 => Some(tSplice(t), a)
          case ty =>
            throw ElaborateError(
              s"cannot adjust stage (1) of ${ctx.pretty(t)}, from ${ctx
                  .pretty(st1)} to ${ctx.pretty(st2)}, got ${ctx.pretty(ty)}"
            )
      case _ =>
        throw ElaborateError(
          s"cannot adjust stage (2) of ${ctx.pretty(t)}, from ${ctx
              .pretty(st1)} to ${ctx.pretty(st2)}"
        )

  private def adjustStage(t: Tm, a: VTy, st1: VTy, st2: VTy)(implicit
      ctx: Ctx
  ): (Tm, VTy) =
    debug(s"adjustStage ${ctx.pretty(t)} : ${ctx.pretty(a)} from ${ctx
        .pretty(st1)} to ${ctx.pretty(st2)}")
    tryAdjustStage(t, a, st1, st2).getOrElse((t, a))

  private def coe(t: Tm, a: VTy, st1: VTy, b: VTy, st2: VTy)(implicit
      ctx: Ctx
  ): Tm =
    debug(
      s"coeTop ${ctx.pretty(t)} : ${ctx.pretty(a)} : ${ctx.pretty(st1)} to ${ctx
          .pretty(b)} : ${ctx.pretty(st2)}"
    )
    def pick(x: Bind, y: Bind)(implicit ctx: Ctx): Bind = ctx.fresh((x, y) match
      case (DontBind, DontBind) => DoBind(Name("x"))
      case (DontBind, x)        => x
      case (x, DontBind)        => x
      case (_, x)               => x
    )
    def justAdjust(t: Tm, a: VTy, st1: VTy, b: VTy, st2: VTy)(implicit
        ctx: Ctx
    ): Option[Tm] =
      tryAdjustStage(t, a, st1, st2) match
        case None         => unify(st1, st2); unify(a, b); None
        case Some((t, a)) => unify(st1, st2); unify(a, b); Some(t)
    def go(
        t: Tm,
        a: VTy,
        st1: VTy,
        b: VTy,
        st2: VTy
    )(implicit ctx: Ctx): Option[Tm] =
      debug(
        s"coe ${ctx.pretty(t)} : ${ctx.pretty(a)} : ${ctx.pretty(st1)} to ${ctx
            .pretty(b)} : ${ctx.pretty(st2)}"
      )
      (force(a), force(b)) match
        case (VPi(x1, i1, a1, u11, b1, u12), VPi(x2, i2, a2, u21, b2, u22)) =>
          if i1 != i2 then throw ElaborateError(s"cannot coerce")
          val ctx2 = ctx.bind(x1, a2, u21)
          val coev0 = go(Local(ix0), a2, u21, a1, u11)(ctx2)
          coev0 match
            case None =>
              val body = go(
                App(Wk(t), Local(ix0), i1),
                b1(VVar(ctx.lvl)),
                u12,
                b2(VVar(ctx.lvl)),
                u22
              )(ctx2)
              body.map(Lam(x1, i1, _))
            case Some(coev0) =>
              val body = go(
                App(Wk(t), coev0, i1),
                b1(ctx2.eval(coev0)),
                u12,
                b2(VVar(ctx.lvl)),
                u22
              )(ctx2)
              body match
                case None => Some(Lam(pick(x1, x2), i1, App(Wk(t), coev0, i1)))
                case Some(body) => Some(Lam(pick(x1, x2), i1, body))
        case (VSigma(x1, a1, u11, b1, u12), VSigma(x2, a2, u21, b2, u22)) =>
          val fst = go(Proj(t, Fst), a1, u11, a2, u21)
          val snd = fst match
            case None =>
              go(
                Proj(t, Snd),
                b1(vfst(ctx.eval(t))),
                u12,
                b2(vfst(ctx.eval(t))),
                u22
              )
            case Some(fst) =>
              go(
                Proj(t, Snd),
                b1(vfst(ctx.eval(t))),
                u12,
                b2(ctx.eval(fst)),
                u22
              )
          (fst, snd) match
            case (None, None)           => None
            case (Some(fst), None)      => Some(Pair(fst, Proj(t, Snd)))
            case (None, Some(snd))      => Some(Pair(Proj(t, Fst), snd))
            case (Some(fst), Some(snd)) => Some(Pair(fst, snd))
        case (VU(vf), VU1) => Some(Lift(ctx.quote(vf), t))
        case (VLift(r1, a), VLift(r2, b)) =>
          unify(r1, r2)
          unify(a, b)
          None
        case (VLift(vf, a), b) => Some(coe(tSplice(t), a, VU(vf), b, st2))
        case (a, VLift(vf, b)) => Some(tQuote(coe(t, a, st1, b, VU(vf))))
        case _                 => justAdjust(t, a, st1, b, st2)
    go(t, a, st1, b, st2).getOrElse(t)

  private def check(tm: S.Tm, ty: VTy, univ: VTy)(implicit ctx: Ctx): Tm =
    if !tm.isPos then
      debug(s"check $tm : ${ctx.pretty(ty)} : ${ctx.pretty(univ)}")
    (tm, force(ty)) match
      case (S.Pos(pos, tm), _) => check(tm, ty, univ)(ctx.enter(pos))
      case (S.Hole(x), _)      => newMeta()
      case (S.Lam(x, i1, b), VPi(_, i2, t, u1, rt, u2)) if i1 == i2 =>
        val eb = check(b, rt(VVar(ctx.lvl)), u2)(ctx.bind(x, t, u1))
        Lam(x, i1, eb)
      case (tm, VPi(x, Impl, t, u1, rt, u2)) =>
        val etm = check(tm, rt(VVar(ctx.lvl)), u2)(ctx.bind(x, t, u1, true))
        Lam(x, Impl, etm)

      case (S.Pi(x, i, t, b), VU1) =>
        val et = checkType(t, VU1)
        val eb = checkType(b, VU1)(ctx.bind(x, ctx.eval(et), VU1))
        Pi(x, i, et, U1, eb, U1)
      case (S.Pi(x, i, t, b), VUFun()) =>
        val et = checkType(t, VUVal())
        val (eb, u2, _) = inferType(b)(ctx.bind(x, ctx.eval(et), VUVal()))
        force(u2) match
          case VU1 => throw ElaborateError(s"invalid universes: $tm")
          case _   =>
        Pi(x, i, et, ctx.quote(VUVal()), eb, ctx.quote(u2))

      case (S.Sigma(x, t, b), VU1) =>
        val et = checkType(t, VU1)
        val eb = checkType(b, VU1)(ctx.bind(x, ctx.eval(et), VU1))
        Sigma(x, et, U1, eb, U1)
      case (S.Sigma(x, t, b), VUVal()) =>
        val et = checkType(t, VUVal())
        val eb = checkType(b, VUVal())(ctx.bind(x, ctx.eval(et), VUVal()))
        Sigma(x, et, App(U0, VFVal, Expl), eb, App(U0, VFVal, Expl))
      case (S.Pair(fst, snd), VSigma(x, t, u1, b, u2)) =>
        val efst = check(fst, t, u1)
        val esnd = check(snd, b(ctx.eval(efst)), u2)
        Pair(efst, esnd)

      // case (S.Lift(ty), VType(S1)) =>
      //  Lift(checkType(ty, S0(RVal)))

      case (S.Quote(t), VLift(vf, ty)) =>
        tQuote(check(t, ty, VU(vf)))
      case (t, VLift(vf, ty)) =>
        tQuote(check(t, ty, VU(vf)))

      case (S.Let(x, univ2, ot, v, b), _) if univ == univ2 =>
        val (ev, et, vt) = inferValue(v, ot, univ)
        val eb = check(b, ty, univ)(ctx.define(x, vt, univ, ctx.eval(ev)))
        Let(x, ctx.quote(univ), et, ev, eb)

      case (S.If(c, t, f), _) =>
        val ec = check(c, VBool, VUVal())
        val et = check(t, ty, univ)
        val ef = check(f, ty, univ)
        force(univ) match
          case VUVal() =>
          case VUFun() =>
          case _ => throw ElaborateError(s"if should return in U0 Val: $tm")
        If(ctx.quote(ty), ec, et, ef)

      case (S.Fix(go, x, b, a), _) =>
        val vf = force(univ) match
          case VU(vf) => vf
          case _      => throw ElaborateError(s"fix has to return in U0")
        val (ea, vt) = infer(a, VUVal())
        val fun = vpi("_", vt, VUVal(), univ, _ => ty)
        val eb = check(b, ty, univ)(
          ctx.bind(DoBind(go), fun, VUFun()).bind(DoBind(x), vt, VUVal())
        )
        Fix(go, x, eb, ea)

      case (S.Case(scrut, cs), _) =>
        force(univ) match
          case VU1 => check(S.Quote(tm), ty, univ)
          case VU(vf) =>
            val (escrut, scrutty) = infer(scrut, VUVal())
            val (x, as) = force(scrutty) match
              case VTCon(x, as) => (x, as)
              case _ =>
                throw ElaborateError(
                  s"expected type constructor in case $tm, but got: ${ctx.pretty(scrutty)}"
                )
            val ecs = cs.map((x, b) => (x, check(b, ty, VU(vf))))
            Case(escrut, ctx.quote(ty), ctx.quote(vf), ecs)
          case _ => throw ElaborateError(s"invalid universe in check")

      case (tm, _) =>
        val (etm, ty2, univ2) = insert(infer(tm))
        debug(
          s"check inferred ${ctx.pretty(etm)} : ${ctx.pretty(ty2)} : ${ctx.pretty(univ2)}"
        )
        coe(etm, ty2, univ2, ty, univ)

  private def projIndex(tm: Val, x: Bind, ix: Int, clash: Boolean): Val =
    x match
      case DoBind(x) if !clash => vproj(tm, Named(Some(x), ix))
      case _ =>
        @tailrec
        def go(tm: Val, ix: Int): Val = ix match
          case 0 => vproj(tm, Fst)
          case n => go(vproj(tm, Snd), n - 1)
        go(tm, ix)
  private def projNamed(tm: Val, ty: VTy, x: Name)(implicit
      ctx: Ctx
  ): (ProjType, VTy, VTy) =
    @tailrec
    def go(ty: VTy, ix: Int, ns: Set[Name]): (ProjType, VTy, VTy) =
      force(ty) match
        case VSigma(DoBind(y), fstty, u1, _, _) if x == y =>
          (Named(Some(x), ix), fstty, u1)
        case VSigma(y, _, _, sndty, _) =>
          val (clash, newns) = y match
            case DoBind(y) => (ns.contains(y), ns + y)
            case DontBind  => (false, ns)
          go(sndty(projIndex(tm, y, ix, clash)), ix + 1, newns)
        case _ =>
          throw ElaborateError(
            s"expected sigma in named projection $x, got ${ctx.pretty(ty)}"
          )
    go(ty, 0, Set.empty)

  private def infer(tm: S.Tm, univ: VTy)(implicit ctx: Ctx): (Tm, VTy) =
    if !tm.isPos then debug(s"inferS $tm : ${ctx.pretty(univ)}")
    tm match
      case S.Pos(pos, tm) => infer(tm, univ)(ctx.enter(pos))
      case tm =>
        val (et, vt, univ2) = infer(tm)
        debug(s"inferred ${ctx.pretty(et)}")
        val (et2, vt2) = adjustStage(et, vt, univ2, univ)
        debug(s"adjusted ${ctx.pretty(et2)}")
        (et2, vt2)

  private def infer(tm: S.Tm)(implicit ctx: Ctx): (Tm, VTy, VTy) =
    if !tm.isPos then debug(s"infer $tm")
    tm.removePos match
      case S.Pos(pos, tm)       => infer(tm)(ctx.enter(pos))
      case S.Var(Name("VF"))    => (VF, VU1, VU1)
      case S.Var(Name("Val"))   => (VFVal, VVF, VU1)
      case S.Var(Name("Fun"))   => (VFFun, VVF, VU1)
      case S.Var(Name("U1"))    => (U1, VU1, VU1)
      case S.Var(Name("U0"))    => (U0, vpi("_", VVF, VU1, VU1, _ => VU1), VU1)
      case S.Var(Name("Bool"))  => (Bool, VUVal(), VU1)
      case S.Var(Name("True"))  => (True, VBool, VUVal())
      case S.Var(Name("False")) => (False, VBool, VUVal())
      case S.Var(Name("Int"))   => (IntTy, VUVal(), VU1)
      case S.IntLit(n)          => (IntLit(n), VInt, VUVal())
      case S.App(S.App(S.Var(Name("+")), a, Expl), b, Expl) =>
        val ea = check(a, VInt, VUVal()); val eb = check(b, VInt, VUVal())
        (Binop(OAdd, ea, eb), VInt, VUVal())
      case S.App(S.App(S.Var(Name("*")), a, Expl), b, Expl) =>
        val ea = check(a, VInt, VUVal()); val eb = check(b, VInt, VUVal())
        (Binop(OMul, ea, eb), VInt, VUVal())
      case S.App(S.App(S.Var(Name("-")), a, Expl), b, Expl) =>
        val ea = check(a, VInt, VUVal()); val eb = check(b, VInt, VUVal())
        (Binop(OSub, ea, eb), VInt, VUVal())
      case S.App(S.App(S.Var(Name("/")), a, Expl), b, Expl) =>
        val ea = check(a, VInt, VUVal()); val eb = check(b, VInt, VUVal())
        (Binop(ODiv, ea, eb), VInt, VUVal())
      case S.App(S.App(S.Var(Name("%")), a, Expl), b, Expl) =>
        val ea = check(a, VInt, VUVal()); val eb = check(b, VInt, VUVal())
        (Binop(OMod, ea, eb), VInt, VUVal())
      case S.App(S.App(S.Var(Name("==")), a, Expl), b, Expl) =>
        val ea = check(a, VInt, VUVal()); val eb = check(b, VInt, VUVal())
        (Binop(OEq, ea, eb), VBool, VUVal())
      case S.App(S.App(S.Var(Name("!=")), a, Expl), b, Expl) =>
        val ea = check(a, VInt, VUVal()); val eb = check(b, VInt, VUVal())
        (Binop(ONeq, ea, eb), VBool, VUVal())
      case S.App(S.App(S.Var(Name("<")), a, Expl), b, Expl) =>
        val ea = check(a, VInt, VUVal()); val eb = check(b, VInt, VUVal())
        (Binop(OLt, ea, eb), VBool, VUVal())
      case S.App(S.App(S.Var(Name(">")), a, Expl), b, Expl) =>
        val ea = check(a, VInt, VUVal()); val eb = check(b, VInt, VUVal())
        (Binop(OGt, ea, eb), VBool, VUVal())
      case S.App(S.App(S.Var(Name("<=")), a, Expl), b, Expl) =>
        val ea = check(a, VInt, VUVal()); val eb = check(b, VInt, VUVal())
        (Binop(OLeq, ea, eb), VBool, VUVal())
      case S.App(S.App(S.Var(Name(">=")), a, Expl), b, Expl) =>
        val ea = check(a, VInt, VUVal()); val eb = check(b, VInt, VUVal())
        (Binop(OGeq, ea, eb), VBool, VUVal())
      case S.Var(x) =>
        ctx.lookup(x) match
          case Some((ix, ty, st)) => (Local(ix), ty, st)
          case None =>
            getGlobal(x) match
              case Some(e) => (Global(x), e.vty, e.univ)
              case None    => throw ElaborateError(s"undefined variable $x")
      case S.Let(x, u, t, v, b) =>
        val eu = checkType(u, VU1)
        val veu = ctx.eval(eu)
        val (ev, et, vt) = inferValue(v, t, ctx.eval(eu))
        val (eb, rty, st2) = infer(b)(ctx.define(x, vt, veu, ctx.eval(ev)))
        (Let(x, eu, et, ev, eb), rty, st2)
      case S.Pi(x, i, t, b) =>
        val (et, u1, _) = inferType(t)
        val (eb, u2) = force(u1) match
          case VU1 =>
            val eb = checkType(b, VU1)(ctx.bind(x, ctx.eval(et), VU1))
            (eb, VU1)
          case _ =>
            val (eb, u2, _) = inferType(b)(ctx.bind(x, ctx.eval(et), u1))
            (eb, u2)
        debug(s"pi univs: $tm ~> (${ctx.pretty(u1)}, ${ctx.pretty(u2)})")
        val u3 = (force(u1), force(u2)) match
          case (VU1, VU1)         => VU1
          case (VUVal(), VUFun()) => VUFun()
          case (VUVal(), VUVal()) => VUFun()
          case _ => throw ElaborateError(s"incompatible universes in pi: $tm")
        (Pi(x, i, et, ctx.quote(u1), eb, ctx.quote(u2)), u3, VU1)
      case S.Sigma(x, t, b) =>
        val (et, u1, _) = inferType(t)
        val (eb, u2) = force(u1) match
          case VU1 =>
            val eb = checkType(b, VU1)(ctx.bind(x, ctx.eval(et), VU1))
            (eb, VU1)
          case VUVal() =>
            val eb = checkType(b, VUVal())(ctx.bind(x, ctx.eval(et), VUVal()))
            (eb, VUVal())
          case u =>
            throw ElaborateError(
              s"sigma parameter universe must be U1 or U0 Val, not ${ctx.pretty(u)}"
            )
        (Sigma(x, et, ctx.quote(u1), eb, ctx.quote(u2)), u2, VU1)
      case S.App(f, a, i) =>
        val (ef, fty, st) = i match
          case Impl => infer(f)
          case Expl => insertPi(infer(f))
        force(fty) match
          case VPi(_, i2, t, u1, b, u2) if i == i2 =>
            val ea = check(a, t, u1)
            (App(ef, ea, i), b(ctx.eval(ea)), u2)
          case _ =>
            throw ElaborateError(
              s"pi expected in $tm but got: ${ctx.pretty(fty)}"
            )
      case S.Proj(t, p) =>
        val (et, ty, l1) = insertPi(infer(t))
        (force(ty), p) match
          case (_, S.Named(x)) =>
            val (p, pty, lv) = projNamed(ctx.eval(et), ty, x)
            (Proj(et, p), pty, lv)
          case (VSigma(_, fstty, u1, _, _), S.Fst) => (Proj(et, Fst), fstty, u1)
          case (VSigma(_, _, _, sndty, u2), S.Snd) =>
            (Proj(et, Snd), sndty(vproj(ctx.eval(et), Fst)), u2)
          case _ =>
            throw ElaborateError(
              s"sigma expected in $tm but got: ${ctx.pretty(ty)}"
            )
      case S.Lift(t) =>
        val (et, st, _) = inferType(t)
        val vf = force(st) match
          case VU(vf) => vf
          case _      => throw ElaborateError(s"can only lift types in U0: $tm")
        (Lift(ctx.quote(vf), et), VU1, VU1)
      case S.Quote(t) =>
        val (et, vt, st) = infer(t)
        val vf = force(st) match
          case VU(vf) => vf
          case _      => impossible()
        (tQuote(et), VLift(vf, vt), VU1)
      case S.Splice(t) =>
        val (et1, vt) = infer(t, VU1)
        val vf = force(vt) match
          case VLift(vf, _) => vf
          case _ => throw ElaborateError(s"expected a lifted type in $tm")
        val (et2, vt2) = adjustStage(et1, vt, VU1, VU(vf))
        (et2, vt2, VU(vf))
      case S.Pair(fst, snd) =>
        val (efst, t1, u1) = infer(fst)
        val (esnd, t2, u2) = force(u1) match
          case VU1 =>
            val (esnd, t2) = infer(snd, VU1)
            (esnd, t2, VU1)
          case VUVal() =>
            val (esnd, t2) = infer(snd, VUVal())
            (esnd, t2, VUVal())
          case u =>
            throw ElaborateError(
              s"invalid universe in snd of pair: ${ctx.pretty(u)}"
            )
        (Pair(efst, esnd), VSigma(DontBind, t1, u1, CFun(_ => t2), u2), u2)
      case S.If(c, t, f) =>
        val ec = check(c, VBool, VUVal())
        val (et, vty, u) = infer(t)
        force(u) match
          case VUVal() =>
          case VUFun() =>
          case _       => throw ElaborateError(s"if must return in U0")
        val ef = check(f, vty, u)
        (If(ctx.quote(vty), ec, et, ef), vty, u)
      case S.Hole(_) =>
        val u = ctx.eval(newMeta())
        val ty = ctx.eval(newMeta())
        val tm = newMeta()
        (tm, ty, u)
      case S.Fix(go, x, b, a) =>
        val (ea, vt) = infer(a, VUVal())
        val vf = ctx.eval(newMeta())
        val u = VU(vf)
        val rt = ctx.eval(newMeta())
        val fun = vpi("_", vt, VUVal(), u, _ => rt)
        val eb = check(b, rt, u)(
          ctx.bind(DoBind(go), fun, VUFun()).bind(DoBind(x), vt, VUVal())
        )
        (Fix(go, x, eb, ea), rt, u)
      case _ => throw ElaborateError(s"cannot infer $tm")

  private def elaborate(tm: S.Tm, ty: Option[S.Ty], u: VTy): (Tm, Ty) =
    debug(s"elaborate $tm")
    resetMetas()
    val (etm, ety, _) =
      inferValue(tm, ty, u)(
        Ctx.empty((0, 0))
      ) // TODO: use source position
    (zonk(etm)(lvl0, Nil), zonk(ety)(lvl0, Nil))

  def elaborate(d: S.Def): Def =
    debug(s"elaborate $d")
    d match
      case S.DDef(x, u, t, v) =>
        if getGlobal(x).isDefined then
          throw ElaborateError(s"global is already defined: $x")
        val eu = zonk(checkType(u, VU1)(Ctx.empty((0, 0))))(lvl0, Nil)
        val veu = eval(eu)(Nil)
        val (ev, et) = elaborate(v, t, veu)
        debug(s"$x : $et = $ev")
        setGlobal(GlobalEntry(x, ev, et, eval(ev)(Nil), eval(et)(Nil), veu))
        DDef(x, eu, et, ev)
      case S.DData(x, ps, cs) =>
        val tconty =
          ps.foldLeft(VUVal())((rt, _) => vpi("_", VUVal(), VU1, VU1, _ => rt))
        val rt =
          TCon(x, (0 until ps.size).reverse.map(i => Local(mkIx(i))).toList)
        val lam = ps.foldRight(rt)((p, b) => Lam(DoBind(p), Expl, b))
        val tcon =
          setGlobal(
            GlobalEntry(
              x,
              lam,
              quote(tconty)(lvl0),
              eval(lam)(Nil),
              tconty,
              VU1
            )
          )
        implicit val ctx: Ctx =
          ps.foldLeft(Ctx.empty((0, 0)))((ctx, p) =>
            ctx.bind(DoBind(p), VUVal(), VU1)
          )
        val ecs = cs.map((c, ts) => {
          val ets = ts.map(t => {
            val et = check(t, VUVal(), VU1)
            zonk(et)(lvl0, Nil)
          })
          val ty1 = ets.foldRight(Lift(VFVal, rt))((p, rt) =>
            Pi(DontBind, Expl, Lift(VFVal, p), U1, Wk(rt), U1)
          )
          val ty2 = ps.foldRight(ty1)((p, rt) =>
            Pi(DoBind(p), Impl, quote(VUVal())(lvl0), U1, rt, U1)
          )
          val inner = Quote(
            Con(
              c,
              wk(ets.size, rt),
              (0 until ets.size).reverse
                .map(i => {
                  val tm = Splice(Local(mkIx(i)))
                  val ety = ets(ets.size - i - 1)
                  val ty = wk(ets.size, ety)
                  val poly = ety match
                    case Local(_) => true
                    case _        => false
                  (tm, ty, poly)
                })
                .toList
            )
          )
          val lam1 = (0 until ets.size).foldRight(inner)((i, b) =>
            Lam(DoBind(Name(s"a$i")), Expl, b)
          )
          val lam2 = ps.foldRight(lam1)((p, b) => Lam(DoBind(p), Impl, b))
          setGlobal(
            GlobalEntry(c, lam2, ty2, eval(lam2)(Nil), eval(ty2)(Nil), VU1)
          )
          (c, ets)
        })
        DData(x, ps, ecs)

  def elaborate(ds: S.Defs): Defs = Defs(ds.toList.map(elaborate))
