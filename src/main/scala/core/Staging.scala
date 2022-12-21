package core

import common.Common.*
import common.Debug.debug
import Syntax.*
import ir.Syntax as IR
import Globals.getGlobal

import scala.collection.mutable

object Staging:
  private enum Env:
    case Empty
    case Def0(env: Env, value: Val0)
    case Def1(env: Env, value: Val1)

    def tail: Env = this match
      case Def0(e, _) => e
      case Def1(e, _) => e
      case _          => impossible()

    def size: Int = this match
      case Def0(e, _) => 1 + e.size
      case Def1(e, _) => 1 + e.size
      case Empty      => 0
  import Env.*

  private enum Val1:
    case VLam1(body: Val1 => Val1)
    case VQuote(tm: Val0)
    case VType1
    case VVFVal1
    case VVFFun1
    case VU1
    case VU0
    case VU0app(arg: Val1)
    case VBool1
    case VInt1
    case VFun1(left: Val1, vf: Val1, right: Val1 => Val1)
    case VPairTy1(fst: Val1, snd: Val1 => Val1)
    case VPair1(fst: Val1, snd: Val1)
    case VTCon1(name: Name, args: List[Val1])
    case VPoly1
  import Val1.*

  private enum Val0:
    case VVar0(lvl: Lvl)
    case VGlobal0(name: Name)
    case VApp0(fn: Val0, arg: Val0)
    case VLam0(name: Bind, body: Val0 => Val0)
    case VFix0(go: Name, name: Name, body: (Val0, Val0) => Val0, arg: Val0)
    case VLet0(name: Name, vf: Val1, ty: Val1, value: Val0, body: Val0 => Val0)
    case VPair0(fst: Val0, snd: Val0)
    case VFst0(tm: Val0)
    case VSnd0(tm: Val0)
    case VTrue0
    case VFalse0
    case VIf0(ty: Val1, cond: Val0, ifTrue: Val0, ifFalse: Val0)
    case VIntLit0(value: Int)
    case VBinop0(op: Op, left: Val0, right: Val0)
    case VCon0(name: Name, ty: Val1, args: List[(Val0, Val1, Boolean)])
    case VCase0(scrut: Val0, ty: Val1, vf: Val1, cs: List[(Name, Val0)])
  import Val0.*

  private def vvar1(ix: Ix)(implicit env: Env): Val1 =
    def go(env: Env, i: Int): Val1 = (env, i) match
      case (Def1(_, v), 0) => v
      case (Def1(e, _), i) => go(e, i - 1)
      case (Def0(e, _), i) => go(e, i - 1)
      case _               => impossible()
    go(env, ix.expose)

  private def vapp1(f: Val1, a: Val1): Val1 = f match
    case VLam1(f) => f(a)
    case VU0      => VU0app(a)
    case _        => impossible()

  private def vproj1(tm: Val1, proj: ProjType): Val1 = tm match
    case VPair1(fst, snd) =>
      proj match
        case Fst         => fst
        case Snd         => snd
        case Named(_, 0) => fst
        case Named(x, i) => vproj1(snd, Named(x, i - 1))
    case _ => impossible()

  private def eval1Bind(t: Tm, u: Val1)(implicit env: Env): Val1 =
    eval1(t)(Def1(env, u))

  private def eval1(t: Tm)(implicit env: Env): Val1 = t match
    case Local(ix)          => vvar1(ix)
    case Global(x)          => eval1(getGlobal(x).get.tm)
    case Let(_, _, _, v, b) => eval1(b)(Def1(env, eval1(v)))

    case VFVal => VVFVal1
    case VFFun => VVFFun1
    case U0    => VU0
    case U1    => VU1

    case Bool  => VBool1
    case IntTy => VInt1

    case Sigma(_, a, _, b, _) => VPairTy1(eval1(a), v => eval1Bind(b, v))
    case Pair(fst, snd)       => VPair1(eval1(fst), eval1(snd))
    case Proj(t, p)           => vproj1(eval1(t), p)

    case Pi(x, _, a, _, b, u) => VFun1(eval1(a), eval1(u), v => eval1Bind(b, v))
    case Lam(x, _, b)         => VLam1(v => eval1Bind(b, v))
    case App(f, a, _)         => vapp1(eval1(f), eval1(a))

    case Lift(rep, t) => VType1
    case Quote(t)     => VQuote(eval0(t))
    case Splice(t)    => impossible()

    case Wk(t) => eval1(t)(env.tail)

    case TCon(x, as) => VTCon1(x, as.map(eval1))

    case _ => impossible()

  private def vvar0(ix: Ix)(implicit env: Env): Val0 =
    def go(env: Env, i: Int): Val0 = (env, i) match
      case (Def0(_, v), 0) => v
      case (Def0(e, _), i) => go(e, i - 1)
      case (Def1(e, _), i) => go(e, i - 1)
      case _               => impossible()
    go(env, ix.expose)

  private def vsplice(v: Val1): Val0 = v match
    case VQuote(v) => v
    case _         => impossible()

  private def eval0Bind(t: Tm, u: Val0)(implicit env: Env): Val0 =
    eval0(t)(Def0(env, u))

  private def proj0(v: Val0, p: ProjType): Val0 = p match
    case Fst         => VFst0(v)
    case Snd         => VSnd0(v)
    case Named(_, 0) => VFst0(v)
    case Named(x, n) => proj0(VSnd0(v), Named(x, n - 1))

  private def eval0(t: Tm)(implicit env: Env): Val0 = t match
    case Local(ix)           => vvar0(ix)
    case Global(x)           => VGlobal0(x)
    case Let(x, U1, t, v, b) => impossible()
    case Let(x, u, t, v, b) =>
      VLet0(x, eval1(u), eval1(t), eval0(v), v => eval0Bind(b, v))

    case Lam(x, _, b) => VLam0(x, v => eval0Bind(b, v))
    case Fix(go, x, b, arg) =>
      VFix0(go, x, (v, w) => eval0(b)(Def0(Def0(env, v), w)), eval0(arg))
    case App(f, a, _) => VApp0(eval0(f), eval0(a))

    case Pair(fst, snd) => VPair0(eval0(fst), eval0(snd))
    case Proj(t, p)     => proj0(eval0(t), p)

    case Splice(t) => vsplice(eval1(t))

    case Wk(t) => eval0(t)(env.tail)

    case True           => VTrue0
    case False          => VFalse0
    case If(t, c, a, b) => VIf0(eval1(t), eval0(c), eval0(a), eval0(b))

    case IntLit(n)       => VIntLit0(n)
    case Binop(op, a, b) => VBinop0(op, eval0(a), eval0(b))

    case Con(x, t, as) =>
      VCon0(x, eval1(t), as.map((a, b, p) => (eval0(a), eval1(b), p)))

    case Case(scrut, ty, vf, cs) =>
      VCase0(
        eval0(scrut),
        eval1(ty),
        eval1(vf),
        cs.map((x, b) => (x, eval0(b)))
      )

    case _ => impossible()

  // staging
  private enum Tmp:
    case Local(ix: Ix)
    case Global(name: Name)
    case Let(name: Name, ty: IR.TDef, value: Tmp, body: Tmp)

    case Lam(name: Bind, body: Tmp)
    case Fix(go: Name, name: Name, body: Tmp, arg: Tmp)
    case App(fn: Tmp, arg: Tmp)

    case Pair(fst: Tmp, snd: Tmp)
    case Fst(tm: Tmp)
    case Snd(tm: Tmp)

    case True
    case False
    case If(ty: IR.TDef, cond: Tmp, ifTrue: Tmp, ifFalse: Tmp)

    case IntLit(value: Int)
    case Binop(op: Op, left: Tmp, right: Tmp)

    case Con(name: Name, ty: IR.Ty, args: List[(Tmp, IR.Ty, Boolean)])
    case Case(scrut: Tmp, ty: IR.TDef, cases: List[(Name, Tmp)])

  private def quote0ir(v: Val0)(implicit k: Lvl): Tmp =
    // debug(s"quote0ir $v")
    v match
      case VVar0(l)    => Tmp.Local(l.toIx)
      case VGlobal0(x) => Tmp.Global(x)
      case VApp0(f, a) => Tmp.App(quote0ir(f), quote0ir(a))
      case VLam0(x, b) => Tmp.Lam(x, quote0ir(b(VVar0(k)))(k + 1))
      case VFix0(go, x, b, arg) =>
        Tmp.Fix(
          go,
          x,
          quote0ir(b(VVar0(k), VVar0(k + 1)))(k + 2),
          quote0ir(arg)
        )
      case VLet0(x, VU0app(VVFVal1), t, v, b) =>
        Tmp.Let(
          x,
          IR.TDef(quote1ty(t)),
          quote0ir(v),
          quote0ir(b(VVar0(k)))(k + 1)
        )
      case VLet0(x, VU0app(VVFFun1), t, v, b) =>
        Tmp.Let(x, quote1tdef(t), quote0ir(v), quote0ir(b(VVar0(k)))(k + 1))
      case VPair0(fst, snd) => Tmp.Pair(quote0ir(fst), quote0ir(snd))
      case VFst0(t)         => Tmp.Fst(quote0ir(t))
      case VSnd0(t)         => Tmp.Snd(quote0ir(t))
      case VTrue0           => Tmp.True
      case VFalse0          => Tmp.False
      case VIf0(t, c, a, b) =>
        Tmp.If(quote1tdefOrTy(t), quote0ir(c), quote0ir(a), quote0ir(b))
      case VIntLit0(n)       => Tmp.IntLit(n)
      case VBinop0(op, a, b) => Tmp.Binop(op, quote0ir(a), quote0ir(b))
      case VCon0(x, t, as) =>
        Tmp.Con(
          x,
          quote1ty(t),
          as.map((a, b, p) => (quote0ir(a), quote1ty(b), p))
        )
      case VCase0(scrut, ty, _, cs) =>
        Tmp.Case(
          quote0ir(scrut),
          quote1tdefOrTy(ty),
          cs.map((x, b) => (x, quote0ir(b)))
        )
      case _ => impossible()

  private def quote1ty(v: Val1)(implicit k: Lvl): IR.Ty =
    // debug(s"quote1ty $v")
    v match
      case VBool1 => IR.TBool
      case VInt1  => IR.TInt
      case VPairTy1(fst, snd) =>
        IR.TPair(quote1ty(fst), quote1ty(snd(null))(k + 1))
      case VTCon1(x, as) => IR.TCon(x, as.map(quote1ty))
      case VPoly1        => IR.TPoly
      case _             => impossible()

  private def quote1tdef(v: Val1, ps: List[IR.Ty] = Nil)(implicit
      k: Lvl
  ): IR.TDef =
    // debug(s"quote1tdef $v")
    v match
      case VFun1(a, VU0app(VVFVal1), b) =>
        IR.TDef(ps.reverse ++ List(quote1ty(a)), quote1ty(b(null))(k + 1))
      case VFun1(a, VU0app(VVFFun1), b) =>
        quote1tdef(b(null), quote1ty(a) :: ps)(k + 1)
      case t => impossible()

  private def quote1tdefOrTy(v: Val1)(implicit k: Lvl): IR.TDef =
    // debug(s"quote1tdefOrTy $v")
    v match
      case VBool1 => IR.TDef(IR.TBool)
      case VInt1  => IR.TDef(IR.TInt)
      case VPairTy1(fst, snd) =>
        IR.TDef(IR.TPair(quote1ty(fst), quote1ty(snd(null))(k + 1)))
      case VTCon1(x, as) => IR.TDef(IR.TCon(x, as.map(quote1ty)))
      case VPoly1        => IR.TDef(IR.TPoly)
      case _             => quote1tdef(v)

  private def stageIR(tm: Tm): Tmp =
    debug(s"stageIR $tm")
    quote0ir(eval0(tm)(Empty))(lvl0)

  private def stageIRTy(tm: Tm): IR.Ty =
    debug(s"stageIRTy $tm")
    quote1ty(eval1(tm)(Empty))(lvl0)

  private def stageIRTy(env: Env, tm: Tm): IR.Ty =
    debug(s"stageIRTy $tm")
    quote1ty(eval1(tm)(env))(mkLvl(env.size))

  private def stageIRTDef(tm: Tm): IR.TDef =
    debug(s"stageIRDef $tm")
    quote1tdef(eval1(tm)(Empty))(lvl0)

  /* translate to IR
      - use named variables
      - store types in local variables
      - store param and return type in lambda
   */
  private final case class Ctx(
      types: List[IR.TDef],
      names: List[Int]
  ):
    def bind(ty: IR.TDef): (Int, Ctx) =
      val n = if names.isEmpty then 0 else names.max + 1
      (n, Ctx(ty :: types, n :: names))
  private object Ctx:
    def empty: Ctx = Ctx(Nil, Nil)

  private type GlobalsTy = mutable.Map[Name, IR.TDef]

  private def check(tm: Tmp, ty: IR.TDef)(implicit
      ctx: Ctx,
      globals: GlobalsTy
  ): IR.Tm =
    (tm, ty) match
      case (Tmp.Lam(x, b), IR.TDef(pt :: ps, rt)) =>
        val (n, nctx) = ctx.bind(IR.TDef(pt))
        val eb = check(b, IR.TDef(ps, rt))(nctx, globals)
        IR.Lam(n, pt, IR.TDef(ps, rt), eb)
      case (Tmp.Fix(go, x, b, arg), rt) =>
        val (earg, pt) = infer(arg)
        if pt.params.nonEmpty then impossible()
        val (n1, nctx1) = ctx.bind(IR.TDef(pt.retrn, rt))
        val (n2, nctx2) = nctx1.bind(pt)
        val eb = check(b, rt)(nctx2, globals)
        IR.Fix(n1, n2, pt.retrn, rt, eb, earg)
      case (Tmp.Let(x, t, v, b), ty) =>
        val ev = check(v, t)
        val (n, nctx) = ctx.bind(t)
        val eb = check(b, ty)(nctx, globals)
        IR.Let(n, t, ev, eb)
      case _ =>
        val (etm, ty2) = infer(tm)
        if ty2 != ty then impossible()
        etm

  private def check(tm: Tmp, ty: IR.Ty)(implicit
      ctx: Ctx,
      globals: GlobalsTy
  ): IR.Tm = check(tm, IR.TDef(ty))

  private def infer(
      tm: Tmp
  )(implicit ctx: Ctx, globals: GlobalsTy): (IR.Tm, IR.TDef) = tm match
    case Tmp.Local(ix) =>
      val ty = ctx.types(ix.expose)
      val n = ctx.names(ix.expose)
      (IR.Local(n, ty), ty)
    case Tmp.Global(x) =>
      val ty = globals(x)
      (IR.Global(x, ty), ty)
    case Tmp.Let(x, t, v, b) =>
      val ev = check(v, t)
      val (n, nctx) = ctx.bind(t)
      val (eb, rt) = infer(b)(nctx, globals)
      (IR.Let(n, t, ev, eb), rt)

    case Tmp.App(f, a) =>
      val (ef, ft) = infer(f)
      ft match
        case IR.TDef(t :: rest, rt) =>
          val ea = check(a, t)
          (IR.App(ef, ea), IR.TDef(rest, rt))
        case _ => impossible()

    case Tmp.Pair(fst, snd) =>
      val (efst, fstty) = infer(fst)
      val (esnd, sndty) = infer(snd)
      if fstty.params.nonEmpty || sndty.params.nonEmpty then impossible()
      val t1 = fstty.retrn
      val t2 = sndty.retrn
      (IR.Pair(t1, t2, efst, esnd), IR.TDef(IR.TPair(t1, t2)))
    case Tmp.Fst(t) =>
      val (et, ty) = infer(t)
      ty match
        case IR.TDef(Nil, IR.TPair(fst, _)) => (IR.Fst(fst, et), IR.TDef(fst))
        case _                              => impossible()
    case Tmp.Snd(t) =>
      val (et, ty) = infer(t)
      ty match
        case IR.TDef(Nil, IR.TPair(_, snd)) => (IR.Snd(snd, et), IR.TDef(snd))
        case _                              => impossible()

    case Tmp.True  => (IR.True, IR.TDef(IR.TBool))
    case Tmp.False => (IR.False, IR.TDef(IR.TBool))
    case Tmp.If(ty, c, a, b) =>
      val ec = check(c, IR.TBool)
      val ea = check(a, ty)
      val eb = check(b, ty)
      (IR.If(ty, ec, ea, eb), ty)

    case Tmp.IntLit(n) => (IR.IntLit(n), IR.TDef(IR.TInt))

    case Tmp.Binop(op, a, b) =>
      val ea = check(a, IR.TInt); val eb = check(b, IR.TInt)
      val rt = op match
        case OAdd => IR.TInt
        case OMul => IR.TInt
        case OSub => IR.TInt
        case ODiv => IR.TInt
        case OMod => IR.TInt
        case _    => IR.TBool
      (IR.Binop(op, ea, eb), IR.TDef(rt))

    case Tmp.Con(x, t, as) =>
      val eas = as.map((t, ty, p) => {
        val ea = check(t, ty)
        (ea, ty, p)
      })
      (IR.Con(x, t, eas), IR.TDef(t))

    case Tmp.Case(scrut, ty, cs) =>
      val (escrut, scrutty) = infer(scrut)
      val ecs = cs.map((c, b) => (c, check(b, ty)))
      (IR.Case(escrut, ty, ecs), ty)

    case _ => impossible()

  private def stage(d: Def)(implicit globals: GlobalsTy): Option[IR.Def] =
    d match
      case DDef(x, u, t, v) =>
        eval1(u)(Empty) match
          case VU0app(VVFVal1) =>
            val ty = IR.TDef(stageIRTy(t))
            val tm = check(stageIR(v), ty)(Ctx.empty, globals)
            globals += (x -> ty)
            Some(IR.DDef(x, ty, tm))
          case VU0app(VVFFun1) =>
            val ty = stageIRTDef(t)
            val tm = check(stageIR(v), ty)(Ctx.empty, globals)
            globals += (x -> ty)
            Some(IR.DDef(x, ty, tm))
          case _ => None
      case DData(x, ps, cs) =>
        val env = ps.foldLeft(Empty)((env, _) => Def1(env, VPoly1))
        Some(IR.DData(x, ps, cs.map((c, as) => (c, as.map(stageIRTy(env, _))))))

  def stage(ds: Defs): IR.Defs =
    implicit val globals: GlobalsTy = mutable.Map.empty
    IR.Defs(ds.toList.flatMap(stage))
