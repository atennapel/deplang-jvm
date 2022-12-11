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
  import Val1.*

  private enum Val0:
    case VVar0(lvl: Lvl)
    case VGlobal0(name: Name)
    case VApp0(fn: Val0, arg: Val0)
    case VPi0(name: Bind, rep: Rep, ty: Val0, body: Val0 => Val0)
    case VLam0(name: Bind, body: Val0 => Val0)
    case VLet0(name: Name, rep: Rep, ty: Val0, value: Val0, body: Val0 => Val0)
    case VPairTy0(fst: Val0, snd: Val0)
    case VPair0(fst: Val0, snd: Val0)
    case VFst0(tm: Val0)
    case VSnd0(tm: Val0)
    case VType0(rep: Rep)
    case VNat0
    case VZ0
    case VS0(n: Val0)
    case VFoldNat0(ty: Val0)
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
    case _        => impossible()

  private def eval1Bind(t: Tm, u: Val1)(implicit env: Env): Val1 =
    eval1(t)(Def1(env, u))

  private def eval1(t: Tm)(implicit env: Env): Val1 = t match
    case Local(ix)          => vvar1(ix)
    case Global(x)          => eval1(getGlobal(x).get.tm)
    case Let(_, _, _, v, b) => eval1(b)(Def1(env, eval1(v)))

    case Type(s) => VType1

    case Pi(x, t, st, b) => VType1
    case Lam(x, b)       => VLam1(v => eval1Bind(b, v))
    case App(f, a)       => vapp1(eval1(f), eval1(a))

    case PairTy(_, _) => impossible()
    case Pair(_, _)   => impossible()
    case Fst(_)       => impossible()
    case Snd(_)       => impossible()

    case Lift(rep, t) => VType1
    case Quote(t)     => VQuote(eval0(t))
    case Splice(t)    => impossible()

    case Wk(t) => eval1(t)(env.tail)

    case Nat        => impossible()
    case Z          => impossible()
    case S(_)       => impossible()
    case FoldNat(_) => impossible()

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
    case Local(ix) => vvar0(ix)
    case Global(x) => VGlobal0(x)
    case Let(x, S0(rep), t, v, b) =>
      VLet0(x, rep, eval0(t), eval0(v), v => eval0Bind(b, v))
    case Let(_, _, _, _, _) => impossible()

    case Type(S0(rep)) => VType0(rep)
    case Type(S1)      => impossible()

    case Pi(x, t, S0(rep), b) => VPi0(x, rep, eval0(t), v => eval0Bind(b, v))
    case Pi(_, _, _, _)       => impossible()
    case Lam(x, b)            => VLam0(x, v => eval0Bind(b, v))
    case App(f, a)            => VApp0(eval0(f), eval0(a))

    case PairTy(fst, snd) => VPairTy0(eval0(fst), eval0(snd))
    case Pair(fst, snd)   => VPair0(eval0(fst), eval0(snd))
    case Fst(t)           => VFst0(eval0(t))
    case Snd(t)           => VSnd0(eval0(t))

    case Lift(rep, t) => impossible()
    case Quote(t)     => impossible()
    case Splice(t)    => vsplice(eval1(t))

    case Wk(t) => eval0(t)(env.tail)

    case Nat        => VNat0
    case Z          => VZ0
    case S(n)       => VS0(eval0(n))
    case FoldNat(t) => VFoldNat0(eval0(t))

  private def quote0ir(v: Val0)(implicit k: Lvl): IR.Tm = v match
    case VVar0(l)           => IR.Local(l.toIx)
    case VGlobal0(x)        => IR.Global(x)
    case VApp0(f, a)        => IR.App(quote0ir(f), quote0ir(a))
    case VPi0(x, rep, t, b) => impossible()
    case VLam0(x, b)        => IR.Lam(x, quote0ir(b(VVar0(k)))(k + 1))
    case VLet0(x, RVal, t, v, b) =>
      IR.Let(x, Left(quote0ty(t)), quote0ir(v), quote0ir(b(VVar0(k)))(k + 1))
    case VLet0(x, RFun, t, v, b) =>
      IR.Let(x, Right(quote0fun(t)), quote0ir(v), quote0ir(b(VVar0(k)))(k + 1))
    case VZ0                => IR.Z
    case VS0(n: Val0)       => IR.S(quote0ir(n))
    case VFoldNat0(t: Val0) => IR.FoldNat(quote0ty(t))
    case VPair0(fst, snd)   => IR.Pair(quote0ir(fst), quote0ir(snd))
    case VFst0(t)           => IR.Fst(quote0ir(t))
    case VSnd0(t)           => IR.Snd(quote0ir(t))
    case _                  => impossible()

  private def quote0ty(v: Val0)(implicit k: Lvl): IR.Ty = v match
    case VNat0              => IR.TNat
    case VPairTy0(fst, snd) => IR.TPair(quote0ty(fst), quote0ty(snd))
    case _                  => impossible()

  private def quote0fun(v: Val0)(implicit k: Lvl): IR.TFun = v match
    case VPi0(_, RVal, t, b) =>
      IR.TFun(quote0ty(t), Left(quote0ty(b(VVar0(k)))(k + 1)))
    case VPi0(_, RFun, t, b) =>
      IR.TFun(quote0ty(t), Right(quote0fun(b(VVar0(k)))(k + 1)))
    case _ => impossible()

  private def stageIR(tm: Tm): IR.Tm =
    debug(s"stageIR $tm")
    quote0ir(eval0(tm)(Empty))(lvl0)

  private def stageIRTy(tm: Tm): IR.Ty =
    debug(s"stageIRTy $tm")
    quote0ty(eval0(tm)(Empty))(lvl0)

  private def stageIRFun(tm: Tm): IR.TFun =
    debug(s"stageIRFun $tm")
    quote0fun(eval0(tm)(Empty))(lvl0)

  private def stage(d: Def): Option[IR.Def] = d match
    case DDef(x, st @ S0(RVal), t, v) =>
      Some(IR.DDef(x, Left(stageIRTy(t)), stageIR(v)))
    case DDef(x, st @ S0(RFun), t, v) =>
      Some(IR.DDef(x, Right(stageIRFun(t)), stageIR(v)))
    case _ => None

  def stage(ds: Defs): IR.Defs = IR.Defs(ds.toList.flatMap(stage))
