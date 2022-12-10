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

  private def inferValue(v: S.Tm, t: Option[S.Ty], st: Stage)(implicit
      ctx: Ctx
  ): (Tm, Ty, VTy) = t match
    case None =>
      val (etm, vty) = infer(v, st)
      (etm, ctx.quote(vty), vty)
    case Some(ty) =>
      val ety = checkType(ty, st.split(_ => S0(RErased), S1))
      val vty = ctx.eval(ety)
      val etm = check(v, vty, st)
      (etm, ety, vty)

  private def checkType(t: S.Ty, st: Stage)(implicit ctx: Ctx): Ty =
    check(t, VType(st), st)

  private def inferType(t: S.Ty)(implicit ctx: Ctx): (Ty, Stage) =
    val (et, vt, st) = infer(t)
    force(vt) match
      case VType(st) => (et, st)
      case _ =>
        throw ElaborateError(s"expected type for $t, but got ${ctx.pretty(vt)}")

  private def tryAdjustStage(t: Tm, a: VTy, st1: Stage, st2: Stage)(implicit
      ctx: Ctx
  ): Option[(Tm, VTy)] =
    debug(
      s"tryAdjustStage ${ctx.pretty(t)} : ${ctx.pretty(a)} from $st1 to $st2"
    )
    (st1, st2) match
      case _ if st1 == st2 => None
      case (S0(rep), S1)   => Some(tQuote(t), VLift(rep, a))
      case (S1, S0(rep)) =>
        force(a) match
          case VLift(rep2, a) if rep == rep2 => Some(tSplice(t), a)
          case _ =>
            throw ElaborateError(
              s"cannot adjust stage of ${ctx.pretty(t)}, from $st1 to $st2"
            )
      case _ =>
        throw ElaborateError(
          s"cannot adjust stage of ${ctx.pretty(t)}, from $st1 to $st2"
        )

  private def adjustStage(t: Tm, a: VTy, st1: Stage, st2: Stage)(implicit
      ctx: Ctx
  ): (Tm, VTy) =
    debug(s"adjustStage ${ctx.pretty(t)} : ${ctx.pretty(a)} from $st1 to $st2")
    tryAdjustStage(t, a, st1, st2).getOrElse((t, a))

  private def coe(t: Tm, a: VTy, st1: Stage, b: VTy, st2: Stage)(implicit
      ctx: Ctx
  ): Tm =
    def pick(x: Bind, y: Bind)(implicit ctx: Ctx): Bind = ctx.fresh((x, y) match
      case (DontBind, DontBind) => DoBind(Name("x"))
      case (DontBind, x)        => x
      case (x, DontBind)        => x
      case (_, x)               => x
    )
    def justAdjust(t: Tm, a: VTy, st1: Stage, b: VTy, st2: Stage)(implicit
        ctx: Ctx
    ): Option[Tm] =
      tryAdjustStage(t, a, st1, st2) match
        case None         => unify(a, b); None
        case Some((t, a)) => unify(a, b); Some(t)
    def go(
        t: Tm,
        a: VTy,
        st1: Stage,
        b: VTy,
        st2: Stage
    )(implicit ctx: Ctx): Option[Tm] =
      debug(
        s"coe ${ctx.pretty(t)} : ${ctx.pretty(a)} : $st1 to ${ctx.pretty(b)} : $st2"
      )
      (force(a), force(b)) match
        case (VPi(x1, a1, rst1, b1), VPi(x2, a2, rst2, b2)) =>
          val ctx2 = ctx.bind(x1, a2, st2)
          val coev0 = go(Local(ix0), a2, st2, a1, st1)(ctx2)
          coev0 match
            case None =>
              val body = go(
                App(Wk(t), Local(ix0)),
                b1(VVar(ctx.lvl)),
                rst1,
                b2(VVar(ctx.lvl)),
                rst2
              )(ctx2)
              body.map(Lam(x1, _))
            case Some(coev0) =>
              val body = go(
                App(Wk(t), coev0),
                b1(ctx2.eval(coev0)),
                rst1,
                b2(VVar(ctx.lvl)),
                rst2
              )(ctx2)
              body match
                case None       => Some(Lam(pick(x1, x2), App(Wk(t), coev0)))
                case Some(body) => Some(Lam(pick(x1, x2), body))
        case (VType(S0(rep)), VType(S1)) => Some(Lift(rep, t))
        case (VLift(r1, a), VLift(r2, b)) =>
          if r1 != r2 then throw ElaborateError(s"Rep mismatch $r1 != $r2")
          unify(a, b)
          None
        case (VLift(rep, a), b) => Some(coe(tSplice(t), a, S0(rep), b, st2))
        case (a, VLift(rep, b)) => Some(tQuote(coe(t, a, st1, b, S0(rep))))
        case _                  => justAdjust(t, a, st1, b, st2)
    go(t, a, st1, b, st2).getOrElse(t)

  private def check(tm: S.Tm, ty: VTy, st: Stage)(implicit ctx: Ctx): Tm =
    if !tm.isPos then debug(s"check $tm : ${ctx.pretty(ty)}")
    (tm, force(ty)) match
      case (S.Pos(pos, tm), _) => check(tm, ty, st)(ctx.enter(pos))
      case (S.Hole(x), _) =>
        throw ElaborateError(
          s"hole found _${x.getOrElse("")} : ${ctx.pretty(ty)}"
        )
      case (S.Lam(x, b), VPi(_, t, rst @ S0(_), rt)) =>
        val eb = check(b, rt(VVar(ctx.lvl)), rst)(ctx.bind(x, t, S0(RVal)))
        Lam(x, eb)
      case (S.Lam(x, b), VPi(_, t, rst, rt)) =>
        val eb = check(b, rt(VVar(ctx.lvl)), rst)(ctx.bind(x, t, st))
        Lam(x, eb)

      // case (S.Lift(ty), VType(S1)) =>
      //  Lift(checkType(ty, S0(RVal)))

      case (S.Pi(x, t, b), VType(S1)) =>
        val et = checkType(t, S1)
        val eb = checkType(b, S1)(ctx.bind(x, ctx.eval(et), S1))
        Pi(x, et, S1, eb)
      case (S.Pi(x, t, b), VType(S0(RFun))) =>
        val et = checkType(t, S0(RVal))
        val (eb, st) = inferType(b)(ctx.bind(x, ctx.eval(et), S0(RVal)))
        st match
          case S1    => throw ElaborateError(s"wrong staging: $tm")
          case S0(_) =>
        Pi(x, et, st, eb)

      case (S.Quote(t), VLift(rep, ty)) =>
        tQuote(check(t, ty, S0(rep)))
      case (t, VLift(rep, ty)) =>
        tQuote(check(t, ty, S0(rep)))

      case (S.Let(x, st2, ot, v, b), _) if st2 == st =>
        val (ev, et, vt) = inferValue(v, ot, st)
        val eb = check(b, ty, st)(ctx.define(x, vt, st, ctx.eval(ev)))
        Let(x, st, et, ev, eb)

      case (tm, _) =>
        val (etm, ty2, st2) = infer(tm)
        coe(etm, ty2, st2, ty, st)

  private def infer(tm: S.Tm, st: Stage)(implicit ctx: Ctx): (Tm, VTy) =
    if !tm.isPos then debug(s"inferS $tm : $st")
    tm match
      case S.Pos(pos, tm) => infer(tm, st)(ctx.enter(pos))
      case tm =>
        val (et, vt, st2) = infer(tm)
        adjustStage(et, vt, st2, st)

  private def infer(tm: S.Tm)(implicit ctx: Ctx): (Tm, VTy, Stage) =
    if !tm.isPos then debug(s"infer $tm")
    tm match
      case S.Pos(pos, tm)  => infer(tm)(ctx.enter(pos))
      case S.Type(S1)      => (Type(S1), VType(S1), S1)
      case S.Type(S0(rep)) => (Type(S0(rep)), VType(S0(RErased)), S0(RErased))
      case S.Var(Name("Nat")) => (Nat, VType(S0(RVal)), S0(RErased))
      case S.Var(Name("Z"))   => (Z, VNat, S0(RVal))
      case S.App(S.Var(Name("S")), n) =>
        val en = check(n, VNat, S0(RVal))
        (NatS(en), VNat, S0(RVal))
      case S.Var(Name("S")) =>
        (
          Lam(DoBind(Name("x")), NatS(Local(ix0))),
          VPi(DontBind, VNat, S0(RVal), Clos(Nil, Nat)),
          S0(RVal)
        )
      case S.Var(x) =>
        ctx.lookup(x) match
          case Some((ix, ty, st)) => (Local(ix), ty, st)
          case None =>
            getGlobal(x) match
              case Some(e) => (Global(x), e.vty, e.stage)
              case None    => throw ElaborateError(s"undefined variable $x")
      case S.Let(x, st, t, v, b) =>
        val (ev, et, vt) = inferValue(v, t, st)
        val (eb, rty) = infer(b, st)(ctx.define(x, vt, st, ctx.eval(ev)))
        (Let(x, st, et, ev, eb), rty, st)
      case S.Pi(x, t, b) =>
        val (et, st1) = inferType(t)
        val (eb, st2) = st1 match
          case S1 => (checkType(b, S1)(ctx.bind(x, ctx.eval(et), S1)), S1)
          case _  => inferType(b)(ctx.bind(x, ctx.eval(et), st1))
        val (rt, st3) = (st1, st2) match
          case (S1, S1)             => (S1, S1)
          case (S0(RVal), S0(RVal)) => (S0(RVal), S0(RErased))
          case (S0(RVal), S0(RFun)) => (S0(RFun), S0(RErased))
          case _ => throw ElaborateError(s"wrong staging: $tm ($st1, $st2)")
        (Pi(x, et, rt, eb), VType(st3), st3)
      case S.App(f, a) =>
        val (ef, fty, st) = infer(f)
        force(fty) match
          case VPi(_, t, S1, b) =>
            val ea = check(a, t, S1)
            (App(ef, ea), b(ctx.eval(ea)), S1)
          case VPi(_, t, S0(rep), b) =>
            val ea = check(a, t, S0(RVal))
            (App(ef, ea), b(ctx.eval(ea)), S0(rep))
          case _ =>
            throw ElaborateError(
              s"pi expected in $tm but got: ${ctx.pretty(fty)}"
            )
      case S.Lift(t) =>
        val (et, st) = inferType(t)
        val rep = st match
          case S1 => throw ElaborateError(s"can only lift types in Type: $tm")
          case S0(rep) => rep
        (Lift(rep, et), VType(S1), S1)
      case S.Quote(t) =>
        val (et, vt, st) = infer(t)
        val rep = st match
          case S0(rep) => rep
          case S1      => impossible()
        (tQuote(et), VLift(rep, vt), S1)
      case S.Splice(t) =>
        val (et1, vt) = infer(t, S1)
        val rep = force(vt) match
          case VLift(rep, _) => rep
          case _ => throw ElaborateError(s"expected a lifted type in $tm")
        val (et2, vt2) = adjustStage(et1, vt, S1, S0(rep))
        (et2, vt, S0(rep))
      case _ => throw ElaborateError(s"cannot infer $tm")

  private def elaborate(tm: S.Tm, ty: Option[S.Ty], st: Stage): (Tm, Ty) =
    debug(s"elaborate $tm")
    val (etm, ety, _) =
      inferValue(tm, ty, st)(
        Ctx.empty((0, 0))
      ) // TODO: use source position
    (etm, ety)

  def elaborate(d: S.Def): Def =
    debug(s"elaborate $d")
    d match
      case S.DDef(x, st, t, v) =>
        if getGlobal(x).isDefined then
          throw ElaborateError(s"global is already defined: $x")
        val (ev, et) = elaborate(v, t, st)
        setGlobal(GlobalEntry(x, ev, et, eval(ev)(Nil), eval(et)(Nil), st))
        DDef(x, st, et, ev)

  def elaborate(ds: S.Defs): Defs = Defs(ds.toList.map(elaborate))
