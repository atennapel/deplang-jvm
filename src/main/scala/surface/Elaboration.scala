package surface

import common.Common.*
import common.Debug.*
import core.Syntax.{S as NatS, *}
import core.Value.*
import core.Evaluation.*
import core.Unification.{unify as unify0, UnifyError}
import core.Globals.*
import Ctx.*
import Syntax as S

object Elaboration:
  final case class ElaborateError(msg: String) extends Exception(msg)

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
        case None         => unify(a, b); None
        case Some((t, a)) => unify(a, b); Some(t)
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
        case (VPi(x1, a1, b1), VFun(a2, u2, b2)) =>
          val x1 = DoBind(Name("x"))
          val ctx2 = ctx.bind(x1, a2, VUVal())
          val coev0 = go(Local(ix0), a2, VUVal(), a1, VU1)(ctx2)
          coev0 match
            case None =>
              val body =
                go(App(Wk(t), Local(ix0)), b1(VVar(ctx.lvl)), VU1, b2, u2)(ctx2)
              body.map(Lam(x1, _))
            case Some(coev0) =>
              val body =
                go(App(Wk(t), coev0), b1(ctx2.eval(coev0)), VU1, b2, u2)(ctx2)
              body match
                case None       => Some(Lam(x1, App(Wk(t), coev0)))
                case Some(body) => Some(Lam(x1, body))
        case (VFun(a1, u1, b1), VPi(x2, a2, b2)) =>
          val x1 = DoBind(Name("x"))
          val ctx2 = ctx.bind(x1, a2, VU1)
          val coev0 = go(Local(ix0), a2, VU1, a1, VUVal())(ctx2)
          coev0 match
            case None =>
              val body =
                go(App(Wk(t), Local(ix0)), b1, u1, b2(VVar(ctx.lvl)), VU1)(ctx2)
              body.map(Lam(x1, _))
            case Some(coev0) =>
              val body =
                go(App(Wk(t), coev0), b1, u1, b2(VVar(ctx.lvl)), VU1)(ctx2)
              body match
                case None       => Some(Lam(x1, App(Wk(t), coev0)))
                case Some(body) => Some(Lam(x1, body))
        case (VFun(a1, u1, b1), VFun(a2, u2, b2)) =>
          val x1 = DoBind(Name("x"))
          val ctx2 = ctx.bind(x1, a2, VUVal())
          val coev0 = go(Local(ix0), a2, VUVal(), a1, VUVal())(ctx2)
          coev0 match
            case None =>
              val body = go(App(Wk(t), Local(ix0)), b1, u1, b2, u2)(ctx2)
              body.map(Lam(x1, _))
            case Some(coev0) =>
              val body = go(App(Wk(t), coev0), b1, u1, b2, u2)(ctx2)
              body match
                case None       => Some(Lam(x1, App(Wk(t), coev0)))
                case Some(body) => Some(Lam(x1, body))
        case (VPi(x1, a1, b1), VPi(x2, a2, b2)) =>
          val ctx2 = ctx.bind(x1, a2, st2)
          val coev0 = go(Local(ix0), a2, VU1, a1, VU1)(ctx2)
          coev0 match
            case None =>
              val body = go(
                App(Wk(t), Local(ix0)),
                b1(VVar(ctx.lvl)),
                VU1,
                b2(VVar(ctx.lvl)),
                VU1
              )(ctx2)
              body.map(Lam(x1, _))
            case Some(coev0) =>
              val body = go(
                App(Wk(t), coev0),
                b1(ctx2.eval(coev0)),
                VU1,
                b2(VVar(ctx.lvl)),
                VU1
              )(ctx2)
              body match
                case None       => Some(Lam(pick(x1, x2), App(Wk(t), coev0)))
                case Some(body) => Some(Lam(pick(x1, x2), body))
        case (VU(vf), VU1) => Some(Lift(ctx.quote(vf), t))
        case (VLift(r1, a), VLift(r2, b)) =>
          if r1 != r2 then throw ElaborateError(s"Rep mismatch $r1 != $r2")
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
      case (S.Hole(x), _) =>
        throw ElaborateError(
          s"hole found _${x.getOrElse("")} : ${ctx.pretty(ty)}"
        )
      case (S.Lam(x, b), VPi(_, t, rt)) =>
        val eb = check(b, rt(VVar(ctx.lvl)), VU1)(ctx.bind(x, t, VU1))
        Lam(x, eb)
      case (S.Lam(x, b), VFun(t1, u, t2)) =>
        val eb = check(b, t2, u)(ctx.bind(x, t1, VUVal()))
        Lam(x, eb)

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

      case (tm, _) =>
        val (etm, ty2, univ2) = infer(tm)
        debug(
          s"check inferred ${ctx.pretty(etm)} : ${ctx.pretty(ty2)} : ${ctx.pretty(univ2)}"
        )
        coe(etm, ty2, univ2, ty, univ)

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
      case S.Pos(pos, tm)     => infer(tm)(ctx.enter(pos))
      case S.Var(Name("VF"))  => (VF, VU1, VU1)
      case S.Var(Name("Val")) => (VFVal, VVF, VU1)
      case S.Var(Name("Fun")) => (VFFun, VVF, VU1)
      case S.Var(Name("U1"))  => (U1, VU1, VU1)
      case S.Var(Name("U0"))  => (U0, vpi("_", VVF, _ => VU1), VU1)
      case S.App(S.Var(Name("fst")), t) =>
        val (et, vt, st) = infer(t)
        force(vt) match
          case VPairTy(fst, snd) => (Fst(et), fst, VUVal())
          case _ => throw ElaborateError(s"expected pair type in $tm")
      case S.App(S.Var(Name("snd")), t) =>
        val (et, vt, st) = infer(t)
        force(vt) match
          case VPairTy(fst, snd) => (Snd(et), snd, VUVal())
          case _ => throw ElaborateError(s"expected pair type in $tm")
      case S.Var(Name("Nat")) => (Nat, VUVal(), VU1)
      case S.Var(Name("Z"))   => (Z, VNat, VUVal())
      case S.App(S.Var(Name("S")), n) =>
        val en = check(n, VNat, VUVal())
        (NatS(en), VNat, VUVal())
      case S.Var(Name("S")) =>
        (
          Lam(DoBind(Name("x")), NatS(Local(ix0))),
          VFun(VNat, VUVal(), VNat),
          VUFun()
        )
      /*
      n : Nat
      z : A
      s : Nat -> A -> A
      --------------------------------------
      foldNat n z s ~> foldNat {A} n z s : A
       */
      case S.App(S.App(S.App(S.Var(Name("foldNat")), n), z), s) =>
        val en = check(n, VNat, VUVal())
        val (ez, vt) = infer(z, VUVal())
        val es = check(
          s,
          VFun(VNat, VUFun(), VFun(vt, VUVal(), vt)),
          VUFun()
        )
        (App(App(App(FoldNat(ctx.quote(vt)), en), ez), es), vt, VUVal())
      case S.Var(Name("foldNat")) =>
        throw ElaborateError(s"foldNat must be fully applied")
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
      case S.Fun(a, b) =>
        val ea = checkType(a, VUVal())
        val (eb, vt, ub) = inferType(b)
        force(vt) match
          case VU1 => throw ElaborateError(s"=> return type cannot be in U1")
          case _   =>
        (Fun(ea, ctx.quote(vt), eb), VUFun(), VU1)
      case S.Pi(x, t, b) =>
        val et = checkType(t, VU1)
        val eb = checkType(b, VU1)(ctx.bind(x, ctx.eval(et), VU1))
        (Pi(x, et, eb), VU1, VU1)
      case S.App(f, a) =>
        val (ef, fty, st) = infer(f)
        force(fty) match
          case VFun(t1, u, t2) =>
            val ea = check(a, t1, VUVal())
            (App(ef, ea), t2, u)
          case VPi(_, t, b) =>
            val ea = check(a, t, VU1)
            (App(ef, ea), b(ctx.eval(ea)), VU1)
          case _ =>
            throw ElaborateError(
              s"pi expected in $tm but got: ${ctx.pretty(fty)}"
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
      case S.PairTy(fst, snd) =>
        val efst = checkType(fst, VUVal())
        val esnd = checkType(snd, VUVal())
        (PairTy(efst, esnd), VUVal(), VU1)
      case S.Pair(fst, snd) =>
        val (efst, t1) = infer(fst, VUVal())
        val (esnd, t2) = infer(snd, VUVal())
        (Pair(efst, esnd), VPairTy(t1, t2), VUVal())
      case _ => throw ElaborateError(s"cannot infer $tm")

  private def elaborate(tm: S.Tm, ty: Option[S.Ty], u: VTy): (Tm, Ty) =
    debug(s"elaborate $tm")
    val (etm, ety, _) =
      inferValue(tm, ty, u)(
        Ctx.empty((0, 0))
      ) // TODO: use source position
    (etm, ety)

  def elaborate(d: S.Def): Def =
    debug(s"elaborate $d")
    d match
      case S.DDef(x, u, t, v) =>
        if getGlobal(x).isDefined then
          throw ElaborateError(s"global is already defined: $x")
        val eu = checkType(u, VU1)(Ctx.empty((0, 0)))
        val veu = eval(eu)(Nil)
        val (ev, et) = elaborate(v, t, veu)
        setGlobal(GlobalEntry(x, ev, et, eval(ev)(Nil), eval(et)(Nil), veu))
        DDef(x, eu, et, ev)

  def elaborate(ds: S.Defs): Defs = Defs(ds.toList.map(elaborate))
