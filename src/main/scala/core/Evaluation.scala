package core

import common.Common.*
import Globals.getGlobal
import Syntax.*
import Value.*
import Metas.*

object Evaluation:
  extension (c: Clos)
    def apply(v: Val): Val = c match
      case CClos(env, tm) => eval(tm)(v :: env)
      case CFun(f)        => f(v)

  def vapp(f: Val, a: Val, i: Icit): Val = f match
    case VLam(_, _, b)     => b(a)
    case VRigid(hd, sp)    => VRigid(hd, SApp(sp, a, i))
    case VFlex(id, sp)     => VFlex(id, SApp(sp, a, i))
    case VGlobal(x, sp, v) => VGlobal(x, SApp(sp, a, i), () => vapp(v(), a, i))
    case _                 => impossible()

  def vquote(v: Val): Val = v match
    case VRigid(hd, SSplice(sp))     => VRigid(hd, sp)
    case VFlex(hd, SSplice(sp))      => VFlex(hd, sp)
    case VGlobal(hd, SSplice(sp), v) => VGlobal(hd, sp, () => vquote(v()))
    case v                           => VQuote(v)

  def vsplice(v: Val): Val = v match
    case VQuote(v)         => v
    case VRigid(hd, sp)    => VRigid(hd, SSplice(sp))
    case VFlex(hd, sp)     => VFlex(hd, SSplice(sp))
    case VGlobal(x, sp, v) => VGlobal(x, SSplice(sp), () => vsplice(v()))
    case _                 => impossible()

  def vfoldnat(t: VTy, n: Val, z: Val, s: Val): Val = n match
    case VZ => z
    // foldNat {t} (S n) z s ~> s n (foldNat {t} n z s)
    case VS(n)          => vapp(vapp(s, n, Expl), vfoldnat(t, n, z, s), Expl)
    case VRigid(hd, sp) => VRigid(hd, SFoldNat(sp, t, z, s))
    case VFlex(hd, sp)  => VFlex(hd, SFoldNat(sp, t, z, s))
    case VGlobal(x, sp, v) =>
      VGlobal(x, SFoldNat(sp, t, z, s), () => vfoldnat(t, v(), z, s))
    case _ => impossible()

  def vfst(v: Val): Val = v match
    case VPair(fst, snd)   => fst
    case VRigid(hd, sp)    => VRigid(hd, SFst(sp))
    case VFlex(hd, sp)     => VFlex(hd, SFst(sp))
    case VGlobal(x, sp, v) => VGlobal(x, SFst(sp), () => vfst(v()))
    case _                 => impossible()

  def vsnd(v: Val): Val = v match
    case VPair(fst, snd)   => snd
    case VRigid(hd, sp)    => VRigid(hd, SSnd(sp))
    case VFlex(hd, sp)     => VFlex(hd, SSnd(sp))
    case VGlobal(x, sp, v) => VGlobal(x, SSnd(sp), () => vsnd(v()))
    case _                 => impossible()

  def vmeta(id: MetaId): Val = getMeta(id) match
    case Unsolved     => VMeta(id)
    case Solved(v, _) => v

  def vappbds(v: Val, bds: BDs)(implicit env: Env): Val = (env, bds) match
    case (Nil, Nil)               => v
    case (t :: env, false :: bds) => vapp(vappbds(v, bds)(env), t, Expl)
    case (t :: env, true :: bds)  => vappbds(v, bds)
    case _                        => impossible()

  def eval(tm: Tm)(implicit env: Env): Val = tm match
    case Local(ix) => env(ix.expose)
    case Global(x) =>
      getGlobal(x) match
        case Some(e) =>
          val value = e.value
          VGlobal(x, SId, () => value)
        case None => impossible()
    case Let(_, _, _, v, b) => eval(b)(eval(v) :: env)

    case VF    => VVF
    case VFVal => VVFVal
    case VFFun => VVFFun
    case U0    => VU0()
    case U1    => VU1

    case Pi(x, i, t, u1, b, u2) =>
      VPi(x, i, eval(t), eval(u1), Clos(b), eval(u2))
    case Lam(x, i, b) => VLam(x, i, Clos(b))
    case App(f, a, i) => vapp(eval(f), eval(a), i)

    case PairTy(fst, snd) => VPairTy(eval(fst), eval(snd))
    case Pair(fst, snd)   => VPair(eval(fst), eval(snd))
    case Fst(t)           => vfst(eval(t))
    case Snd(t)           => vsnd(eval(t))

    case Lift(vf, t) => VLift(eval(vf), eval(t))
    case Quote(t)    => vquote(eval(t))
    case Splice(t)   => vsplice(eval(t))

    case Wk(t) => eval(t)(env.tail)

    case Nat  => VNat
    case Z    => VZ
    case S(n) => VS(eval(n))
    case FoldNat(t) =>
      vlam("n", n => vlam("z", z => vlam("s", s => vfoldnat(eval(t), n, z, s))))

    case Meta(id)              => vmeta(id)
    case InsertedMeta(id, bds) => vappbds(vmeta(id), bds)

  enum Unfold:
    case UnfoldMetas
    case UnfoldAll
  export Unfold.*

  def force(v: Val, unfold: Unfold = UnfoldAll): Val =
    v match
      case VGlobal(_, _, v) if unfold == UnfoldAll => force(v(), UnfoldAll)
      case v                                       => v

  private def quote(hd: Tm, sp: Spine, unfold: Unfold)(implicit k: Lvl): Tm =
    sp match
      case SId            => hd
      case SApp(sp, a, i) => App(quote(hd, sp, unfold), quote(a, unfold), i)
      case SSplice(sp)    => Splice(quote(hd, sp, unfold))
      case SFoldNat(sp, t, z, s) =>
        App(
          App(
            App(FoldNat(quote(t, unfold)), quote(hd, sp, unfold), Expl),
            quote(z, unfold),
            Expl
          ),
          quote(s, unfold),
          Expl
        )
      case SFst(sp) => Fst(quote(hd, sp, unfold))
      case SSnd(sp) => Snd(quote(hd, sp, unfold))

  private def quote(b: Clos, unfold: Unfold)(implicit k: Lvl): Tm =
    quote(b(VVar(k)), unfold)(k + 1)

  def quote(h: Head)(implicit k: Lvl): Tm = h match
    case HVar(l) => Local(l.toIx)
    case HU0     => U0

  def quote(v: Val, unfold: Unfold = UnfoldMetas)(implicit k: Lvl): Tm =
    force(v, unfold) match
      case VRigid(hd, sp)    => quote(quote(hd), sp, unfold)
      case VFlex(hd, sp)     => quote(Meta(hd), sp, unfold)
      case VGlobal(x, sp, v) => quote(Global(x), sp, unfold)

      case VVF    => VF
      case VVFVal => VFVal
      case VVFFun => VFFun
      case VU0()  => U0
      case VU1    => U1

      case VPi(x, i, t, u1, b, u2) =>
        Pi(
          x,
          i,
          quote(t, unfold),
          quote(u1, unfold),
          quote(b, unfold),
          quote(u2, unfold)
        )
      case VLam(x, i, b) => Lam(x, i, quote(b, unfold))

      case VPairTy(fst, snd) => PairTy(quote(fst, unfold), quote(snd, unfold))
      case VPair(fst, snd)   => Pair(quote(fst, unfold), quote(snd, unfold))

      case VLift(vf, v) => Lift(quote(vf, unfold), quote(v, unfold))
      case VQuote(v)    => Quote(quote(v, unfold))

      case VNat  => Nat
      case VZ    => Z
      case VS(n) => S(quote(n, unfold))

  def nf(tm: Tm)(implicit env: Env = Nil): Tm = quote(eval(tm))(mkLvl(env.size))
