package core

import common.Common.*
import Syntax.*
import Value.*
import Evaluation.*
import Metas.*

object Zonking:
  private type VT = Either[Val, Tm]

  private def quoteVT(t: VT)(implicit l: Lvl): Tm =
    t.fold(v => quote(v, UnfoldMetas), t => t)

  private def zonkLift(tm: Tm)(implicit l: Lvl, e: Env): Tm =
    zonk(tm)(l + 1, VVar(l) :: e)

  private def app(f: VT, a: Val, i: Icit)(implicit l: Lvl, e: Env): VT =
    f.fold(v => Left(vapp(v, a, i)), t => Right(App(t, quote(a), i)))

  private def app(f: VT, a: Tm, i: Icit)(implicit l: Lvl, e: Env): VT =
    f.fold(v => Left(vapp(v, eval(a), i)), t => Right(App(t, zonk(a), i)))

  private def fst(t: VT): VT = t.fold(v => Left(vfst(v)), t => Right(Fst(t)))
  private def snd(t: VT): VT = t.fold(v => Left(vsnd(v)), t => Right(Snd(t)))

  private def splice(t: VT): VT =
    t.fold(v => Left(vsplice(v)), t => Right(Splice(t)))

  private def meta(id: MetaId)(implicit l: Lvl, e: Env): VT =
    getMeta(id) match
      case Solved(v, _) => Left(v)
      case Unsolved     => Right(Meta(id))

  private def appbds(id: MetaId, bds: BDs)(implicit l: Lvl, e: Env): VT =
    Left(vappbds(vmeta(id), bds))

  private def zonkSp(t: Tm)(implicit l: Lvl, e: Env): VT = t match
    case Meta(id)              => meta(id)
    case InsertedMeta(id, bds) => appbds(id, bds)
    case App(f, a, i)          => app(zonkSp(f), a, i)
    case Fst(t)                => fst(zonkSp(t))
    case Snd(t)                => snd(zonkSp(t))
    case Splice(t)             => splice(zonkSp(t))
    case Wk(t)                 => zonkSp(t)(l - 1, e.tail).map(Wk(_))
    case t                     => Right(t)

  def zonk(tm: Tm)(implicit l: Lvl, e: Env): Tm = tm match
    case App(f, a, i) => quoteVT(app(zonkSp(f), a, i))
    case Fst(t)       => quoteVT(fst(zonkSp(t)))
    case Snd(t)       => quoteVT(snd(zonkSp(t)))
    case Splice(t)    => quoteVT(splice(zonkSp(t)))

    case Meta(id)              => quoteVT(meta(id))
    case InsertedMeta(id, bds) => quoteVT(appbds(id, bds))

    case Local(ix)          => tm
    case Global(x)          => tm
    case Let(x, u, t, v, b) => Let(x, zonk(u), zonk(t), zonk(v), zonkLift(b))

    case VF    => tm
    case VFVal => tm
    case VFFun => tm
    case U0    => tm
    case U1    => tm

    case Pi(x, i, t, u1, b, u2) =>
      Pi(x, i, zonk(t), zonk(u1), zonkLift(b), zonk(u2))
    case Lam(x, i, b) => Lam(x, i, zonkLift(b))

    case Sigma(x, t, u1, b, u2) =>
      Sigma(x, zonk(t), zonk(u1), zonkLift(b), zonk(u2))
    case PairTy(fst, snd) => PairTy(zonk(fst), zonk(snd))
    case Pair(fst, snd)   => Pair(zonk(fst), zonk(snd))

    case Lift(vf, t) => Lift(zonk(vf), zonk(t))
    case Quote(t)    => Quote(zonk(t))

    case Wk(t) => Wk(zonk(t)(l - 1, e.tail))

    case Nat        => tm
    case Z          => tm
    case S(n)       => S(zonk(n))
    case FoldNat(t) => FoldNat(zonk(t))
