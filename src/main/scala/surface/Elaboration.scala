package surface

import common.Common.*
import common.Globals.*
import common.Debug.*
import core.Syntax.*
import core.Value.*
import core.Evaluation.*
import core.Unification.{unify as unify0, UnifyError}
import Ctx.*
import Syntax as S

object Elaboration:
  final case class ElaborateError(msg: String) extends Exception(msg)

  private def unify(a: VTy, b: VTy)(implicit ctx: Ctx): Unit =
    try unify0(a, b)(ctx.lvl)
    catch
      case e: UnifyError =>
        throw ElaborateError(
          s"cannot unify: ${ctx.quote(a)} ~ ${ctx.quote(b)}: ${e.msg}" // TODO: pretty
        )

  private def inferValue(v: S.Tm, t: Option[S.Ty])(implicit
      ctx: Ctx
  ): (Tm, Ty, VTy) = t match
    case None =>
      val (etm, vty) = infer(v)
      (etm, ctx.quote(vty), vty)
    case Some(ty) =>
      val ety = check(ty, VType)
      val vty = ctx.eval(ety)
      val etm = check(v, vty)
      (etm, ety, vty)

  private def check(tm: S.Tm, ty: VTy)(implicit ctx: Ctx): Tm =
    if !tm.isPos then debug(s"check $tm : ${ctx.quote(ty)}")
    (tm, force(ty)) match
      case (S.Pos(pos, tm), _) => check(tm, ty)(ctx.enter(pos))
      case (S.Hole(x), _) =>
        throw ElaborateError(
          s"hole found _${x.getOrElse("")} : ${ctx.quote(ty)}"
        )
      case (S.Lam(x, b), VPi(_, t, rt)) =>
        val eb = check(b, rt(VVar(ctx.lvl)))(ctx.bind(x, t))
        Lam(x, eb)
      case (S.Let(x, ot, v, b), _) =>
        val (ev, et, vt) = inferValue(v, ot)
        val eb = check(b, ty)(ctx.define(x, vt, ctx.eval(ev)))
        Let(x, et, ev, eb)
      case (tm, _) =>
        val (etm, ty2) = infer(tm)
        unify(ty2, ty)
        etm

  private def infer(tm: S.Tm)(implicit ctx: Ctx): (Tm, VTy) =
    if !tm.isPos then debug(s"infer $tm")
    tm match
      case S.Pos(pos, tm) => infer(tm)(ctx.enter(pos))
      case S.Type         => (Type, VType)
      case S.Var(x) =>
        ctx.lookup(x) match
          case Some((ix, ty)) => (Local(ix), ty)
          case None =>
            getGlobal(x) match
              case Some(e) => (Global(x), e.vty)
              case None    => throw ElaborateError(s"undefined variable $x")
      case S.Let(x, t, v, b) =>
        val (ev, et, vt) = inferValue(v, t)
        val (eb, rty) = infer(b)(ctx.define(x, vt, ctx.eval(ev)))
        (Let(x, et, ev, eb), rty)
      case S.Pi(x, t, b) =>
        val et = check(t, VType)
        val eb = check(b, VType)(ctx.bind(x, ctx.eval(et)))
        (Pi(x, et, eb), VType)
      case S.App(f, a) =>
        val (ef, fty) = infer(f)
        force(fty) match
          case VPi(_, t, b) =>
            val ea = check(a, t)
            (App(ef, ea), b(ctx.eval(ea)))
          case _ =>
            throw ElaborateError(
              s"pi expected in $tm but got: ${ctx.quote(fty)}"
            )
      case _ => throw ElaborateError(s"cannot infer $tm")

  def elaborate(tm: S.Tm, ty: Option[S.Ty] = None): (Tm, Ty) =
    debug(s"elaborate $tm")
    val (etm, ety, _) =
      inferValue(tm, ty)(Ctx.empty((0, 0))) // TODO: use source position
    (etm, ety)

  def elaborate(d: S.Def): Def =
    debug(s"elaborate $d")
    d match
      case S.DDef(x, t, v) =>
        if getGlobal(x).isDefined then
          throw ElaborateError(s"global is already defined: $x")
        val (ev, et) = elaborate(v, t)
        setGlobal(GlobalEntry(x, ev, et, eval(ev)(Nil), eval(et)(Nil)))
        DDef(x, et, ev)

  def elaborate(ds: S.Defs): Defs = Defs(ds.toList.map(elaborate))
