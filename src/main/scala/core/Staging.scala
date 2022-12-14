package core

import common.Common.*
import common.Debug.debug
import Syntax.*
import ir.Syntax as IR
import Globals.getGlobal

object Staging:
  private enum Env:
    case Empty
    case Def0(env: Env, value: Val0)
    case Def1(env: Env, value: Val1)

    def tail: Env = this match
      case Def0(e, _) => e
      case Def1(e, _) => e
      case _          => impossible()
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
    case VNat1
    case VFun1(left: Val1, vf: Val1, right: Val1)
    case VPairTy1(fst: Val1, snd: Val1)
  import Val1.*

  private enum Val0:
    case VVar0(lvl: Lvl)
    case VGlobal0(name: Name)
    case VApp0(fn: Val0, arg: Val0)
    case VLam0(name: Bind, body: Val0 => Val0)
    case VLet0(name: Name, vf: Val1, ty: Val1, value: Val0, body: Val0 => Val0)
    case VPair0(fst: Val0, snd: Val0)
    case VFst0(tm: Val0)
    case VSnd0(tm: Val0)
    case VZ0
    case VS0(n: Val0)
    case VFoldNat0(ty: Val1)
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

    case Nat                  => VNat1
    case Sigma(_, a, _, b, _) => VPairTy1(eval1(a), eval1(b))

    case Pi(x, _, a, _, b, u) => VFun1(eval1(a), eval1(u), eval1(b))
    case Lam(x, _, b)         => VLam1(v => eval1Bind(b, v))
    case App(f, a, _)         => vapp1(eval1(f), eval1(a))

    case Lift(rep, t) => VType1
    case Quote(t)     => VQuote(eval0(t))
    case Splice(t)    => impossible()

    case Wk(t) => eval1(t)(env.tail)

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

  private def eval0(t: Tm)(implicit env: Env): Val0 = t match
    case Local(ix)           => vvar0(ix)
    case Global(x)           => VGlobal0(x)
    case Let(x, U1, t, v, b) => impossible()
    case Let(x, u, t, v, b) =>
      VLet0(x, eval1(u), eval1(t), eval0(v), v => eval0Bind(b, v))

    case Lam(x, _, b) => VLam0(x, v => eval0Bind(b, v))
    case App(f, a, _) => VApp0(eval0(f), eval0(a))

    case Pair(fst, snd) => VPair0(eval0(fst), eval0(snd))
    case Fst(t)         => VFst0(eval0(t))
    case Snd(t)         => VSnd0(eval0(t))

    case Splice(t) => vsplice(eval1(t))

    case Wk(t) => eval0(t)(env.tail)

    case Z          => VZ0
    case S(n)       => VS0(eval0(n))
    case FoldNat(t) => VFoldNat0(eval1(t))

    case _ => impossible()

  private def quote0ir(v: Val0)(implicit k: Lvl): IR.Tm = v match
    case VVar0(l)    => IR.Local(l.toIx)
    case VGlobal0(x) => IR.Global(x)
    case VApp0(f, a) => IR.App(quote0ir(f), quote0ir(a))
    case VLam0(x, b) => IR.Lam(x, quote0ir(b(VVar0(k)))(k + 1))
    case VLet0(x, VU0app(VVFVal1), t, v, b) =>
      IR.Let(
        x,
        IR.TDef(Nil, quote1ty(t)),
        quote0ir(v),
        quote0ir(b(VVar0(k)))(k + 1)
      )
    case VLet0(x, VU0app(VVFFun1), t, v, b) =>
      IR.Let(x, quote1tdef(t), quote0ir(v), quote0ir(b(VVar0(k)))(k + 1))
    case VZ0              => IR.Z
    case VS0(n)           => IR.S(quote0ir(n))
    case VFoldNat0(t)     => IR.FoldNat(quote1ty(t))
    case VPair0(fst, snd) => IR.Pair(quote0ir(fst), quote0ir(snd))
    case VFst0(t)         => IR.Fst(quote0ir(t))
    case VSnd0(t)         => IR.Snd(quote0ir(t))
    case _                => impossible()

  private def quote1ty(v: Val1)(implicit k: Lvl): IR.Ty = v match
    case VNat1              => IR.TNat
    case VPairTy1(fst, snd) => IR.TPair(quote1ty(fst), quote1ty(snd))
    case _                  => impossible()

  private def quote1tdef(v: Val1, ps: List[IR.Ty] = Nil)(implicit
      k: Lvl
  ): IR.TDef = v match
    case VFun1(a, VU0app(VVFVal1), b) =>
      IR.TDef(ps.reverse ++ List(quote1ty(a)), quote1ty(b))
    case VFun1(a, VU0app(VVFFun1), b) => quote1tdef(b, quote1ty(a) :: ps)
    case t                            => impossible()

  private def stageIR(tm: Tm): IR.Tm =
    debug(s"stageIR $tm")
    quote0ir(eval0(tm)(Empty))(lvl0)

  private def stageIRTy(tm: Tm): IR.Ty =
    debug(s"stageIRTy $tm")
    quote1ty(eval1(tm)(Empty))(lvl0)

  private def stageIRTDef(tm: Tm): IR.TDef =
    debug(s"stageIRDef $tm")
    quote1tdef(eval1(tm)(Empty))(lvl0)

  private def stage(d: Def): Option[IR.Def] = d match
    case DDef(x, u, t, v) =>
      eval1(u)(Empty) match
        case VU0app(VVFVal1) =>
          Some(IR.DDef(x, IR.TDef(Nil, stageIRTy(t)), stageIR(v)))
        case VU0app(VVFFun1) => Some(IR.DDef(x, stageIRTDef(t), stageIR(v)))
        case _               => None
    case _ => None

  def stage(ds: Defs): IR.Defs = IR.Defs(ds.toList.flatMap(stage))
