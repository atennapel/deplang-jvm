package surface

import common.Common.*
import common.Debug.*
import core.Syntax.{S as NatS, *}
import core.Value.*
import core.Evaluation.*
import core.Unification.{unify as unify0, UnifyError}
import core.Globals.*
import core.Metas.*
import core.Zonking.*
import Ctx.*
import Syntax as S

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
          val fst = go(Fst(t), a1, u11, a2, u21)
          val snd = fst match
            case None =>
              go(
                Snd(t),
                b1(vfst(ctx.eval(t))),
                u12,
                b2(vfst(ctx.eval(t))),
                u22
              )
            case Some(fst) =>
              go(
                Snd(t),
                b1(vfst(ctx.eval(t))),
                u12,
                b2(ctx.eval(fst)),
                u22
              )
          (fst, snd) match
            case (None, None)           => None
            case (Some(fst), None)      => Some(Pair(fst, Snd(t)))
            case (None, Some(snd))      => Some(Pair(Fst(t), snd))
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

      case (tm, _) =>
        val (etm, ty2, univ2) = insert(infer(tm))
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
      case S.Var(Name("U0"))  => (U0, vpi("_", VVF, VU1, VU1, _ => VU1), VU1)
      case S.App(S.Var(Name("fst")), t, Expl) =>
        val (et, vt, st) = insertPi(infer(t))
        force(vt) match
          case VSigma(_, fst, u1, snd, u2) => (Fst(et), fst, u1)
          case _ => throw ElaborateError(s"expected sigma type in $tm")
      case S.App(S.Var(Name("snd")), t, Expl) =>
        val (et, vt, st) = insertPi(infer(t))
        force(vt) match
          case VSigma(_, fst, u1, snd, u2) =>
            (Snd(et), snd(ctx.eval(Fst(et))), u2)
          case _ => throw ElaborateError(s"expected sigma type in $tm")
      case S.Var(Name("Nat")) => (Nat, VUVal(), VU1)
      case S.Var(Name("Z"))   => (Z, VNat, VUVal())
      case S.App(S.Var(Name("S")), n, Expl) =>
        val en = check(n, VNat, VUVal())
        (NatS(en), VNat, VUVal())
      case S.Var(Name("S")) =>
        (
          Lam(DoBind(Name("x")), Expl, NatS(Local(ix0))),
          vpi("_", VNat, VUVal(), VUVal(), _ => VNat),
          VUFun()
        )
      /*
      n : Nat
      z : A
      s : Nat -> A -> A
      --------------------------------------
      foldNat n z s ~> foldNat {A} n z s : A
       */
      case S.App(
            S.App(S.App(S.Var(Name("foldNat")), n, Expl), z, Expl),
            s,
            Expl
          ) =>
        val en = check(n, VNat, VUVal())
        val (ez, vt) = infer(z, VUVal())
        val es = check(
          s,
          vpi(
            "_",
            VNat,
            VUVal(),
            VUFun(),
            _ => vpi("_", vt, VUVal(), VUVal(), _ => vt)
          ),
          VUFun()
        )
        (
          App(App(App(FoldNat(ctx.quote(vt)), en, Expl), ez, Expl), es, Expl),
          vt,
          VUVal()
        )
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
      case S.Hole(_) =>
        val u = ctx.eval(newMeta())
        val ty = ctx.eval(newMeta())
        val tm = newMeta()
        (tm, ty, u)
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
        setGlobal(GlobalEntry(x, ev, et, eval(ev)(Nil), eval(et)(Nil), veu))
        DDef(x, eu, et, ev)

  def elaborate(ds: S.Defs): Defs = Defs(ds.toList.map(elaborate))
