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

  extension (c: Clos2)
    def apply(v: Val, w: Val): Val = c match
      case CClos2(env, tm) => eval(tm)(w :: v :: env)
      case CFun2(f)        => f(v, w)

  private def isNeutral(v: Val): Boolean = v match
    case VRigid(_, _)     => false
    case VFlex(_, _)      => false
    case VGlobal(_, _, _) => false
    case VFix(_, _, _, _) => false
    case _                => true

  def vapp(f: Val, a: Val, i: Icit): Val = f match
    case VLam(_, _, b)                       => b(a)
    case VFix(go, x, b, SId) if isNeutral(a) => b(f, a)
    case VRigid(hd, sp)                      => VRigid(hd, SApp(sp, a, i))
    case VFlex(id, sp)                       => VFlex(id, SApp(sp, a, i))
    case VGlobal(x, sp, v)  => VGlobal(x, SApp(sp, a, i), () => vapp(v(), a, i))
    case VFix(go, x, b, sp) => VFix(go, x, b, SApp(sp, a, i))
    case _                  => impossible()

  def vquote(v: Val): Val = v match
    case VFix(go, x, b, SSplice(sp)) => VFix(go, x, b, sp)
    case VRigid(hd, SSplice(sp))     => VRigid(hd, sp)
    case VFlex(hd, SSplice(sp))      => VFlex(hd, sp)
    case VGlobal(hd, SSplice(sp), v) => VGlobal(hd, sp, () => vquote(v()))
    case v                           => VQuote(v)

  def vsplice(v: Val): Val = v match
    case VQuote(v)          => v
    case VFix(go, x, b, sp) => VFix(go, x, b, SSplice(sp))
    case VRigid(hd, sp)     => VRigid(hd, SSplice(sp))
    case VFlex(hd, sp)      => VFlex(hd, SSplice(sp))
    case VGlobal(x, sp, v)  => VGlobal(x, SSplice(sp), () => vsplice(v()))
    case _                  => impossible()

  def vfoldnat(t: VTy, n: Val, z: Val, s: Val): Val = n match
    case VZ => z
    // foldNat {t} (S n) z s ~> s n (foldNat {t} n z s)
    case VS(n) => vapp(vapp(s, n, Expl), vfoldnat(t, n, z, s), Expl)
    case VFix(go, x, b, sp) => VFix(go, x, b, SFoldNat(sp, t, z, s))
    case VRigid(hd, sp)     => VRigid(hd, SFoldNat(sp, t, z, s))
    case VFlex(hd, sp)      => VFlex(hd, SFoldNat(sp, t, z, s))
    case VGlobal(x, sp, v) =>
      VGlobal(x, SFoldNat(sp, t, z, s), () => vfoldnat(t, v(), z, s))
    case _ => impossible()

  def vproj(tm: Val, proj: ProjType): Val = tm match
    case VPair(fst, snd) =>
      proj match
        case Fst         => fst
        case Snd         => snd
        case Named(_, 0) => fst
        case Named(x, i) => vproj(snd, Named(x, i - 1))
    case VFix(go, x, b, sp) => VFix(go, x, b, SProj(sp, proj))
    case VRigid(hd, sp)     => VRigid(hd, SProj(sp, proj))
    case VFlex(hd, sp)      => VFlex(hd, SProj(sp, proj))
    case VGlobal(x, sp, v) =>
      VGlobal(x, SProj(sp, proj), () => vproj(v(), proj))
    case _ => impossible()

  def vfst(v: Val): Val = vproj(v, Fst)
  def vsnd(v: Val): Val = vproj(v, Snd)

  def vif(c: Val, t: VTy, a: Val, b: Val): Val = c match
    case VTrue               => a
    case VFalse              => b
    case VFix(go, x, bd, sp) => VFix(go, x, bd, SIf(sp, t, a, b))
    case VRigid(hd, sp)      => VRigid(hd, SIf(sp, t, a, b))
    case VFlex(hd, sp)       => VFlex(hd, SIf(sp, t, a, b))
    case VGlobal(x, sp, v) =>
      VGlobal(x, SIf(sp, t, a, b), () => vif(v(), t, a, b))
    case _ => impossible()

  def vbinop(op: Op, a: Val, b: Val): Val = (op, a, b) match
    case (op, VIntLit(n), VIntLit(m)) =>
      op match
        case OAdd => VIntLit(n + m)
        case OMul => VIntLit(n * m)
        case OSub => VIntLit(n - m)
        case ODiv => VIntLit(n / m)
        case OMod => VIntLit(n % m)
        case OEq  => if n == m then VTrue else VFalse
        case ONeq => if n != m then VTrue else VFalse
        case OLt  => if n < m then VTrue else VFalse
        case OGt  => if n > m then VTrue else VFalse
        case OLeq => if n <= m then VTrue else VFalse
        case OGeq => if n >= m then VTrue else VFalse
    case (OAdd, VIntLit(0), x)       => x
    case (OAdd, x, VIntLit(0))       => x
    case (OMul, VIntLit(0), x)       => VIntLit(0)
    case (OMul, x, VIntLit(0))       => VIntLit(0)
    case (OMul, VIntLit(1), x)       => x
    case (OMul, x, VIntLit(1))       => x
    case (ODiv, x, VIntLit(1))       => x
    case (OSub, x, VIntLit(0))       => x
    case (_, VFix(go, x, bd, sp), _) => VFix(go, x, bd, SBinop(sp, op, b))
    case (_, VRigid(hd, sp), _)      => VRigid(hd, SBinop(sp, op, b))
    case (_, VFlex(hd, sp), _)       => VFlex(hd, SBinop(sp, op, b))
    case (_, VGlobal(x, sp, v), _) =>
      VGlobal(x, SBinop(sp, op, b), () => vbinop(op, v(), b))
    case _ => impossible()

  def vspine(v: Val, sp: Spine): Val = sp match
    case SId                   => v
    case SApp(sp, a, i)        => vapp(vspine(v, sp), a, i)
    case SSplice(sp)           => vsplice(vspine(v, sp))
    case SFoldNat(sp, t, z, s) => vfoldnat(t, vspine(v, sp), z, s)
    case SProj(sp, p)          => vproj(vspine(v, sp), p)
    case SIf(sp, t, a, b)      => vif(vspine(v, sp), t, a, b)
    case SBinop(a, op, b)      => vbinop(op, vspine(v, sp), b)

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
    case Lam(x, i, b)  => VLam(x, i, Clos(b))
    case App(f, a, i)  => vapp(eval(f), eval(a), i)
    case Fix(go, x, b) => VFix(go, x, CClos2(env, b), SId)

    case Sigma(x, t, u1, b, u2) =>
      VSigma(x, eval(t), eval(u1), Clos(b), eval(u2))
    case Pair(fst, snd) => VPair(eval(fst), eval(snd))
    case Proj(t, p)     => vproj(eval(t), p)

    case Lift(vf, t) => VLift(eval(vf), eval(t))
    case Quote(t)    => vquote(eval(t))
    case Splice(t)   => vsplice(eval(t))

    case Wk(t) => eval(t)(env.tail)

    case Nat  => VNat
    case Z    => VZ
    case S(n) => VS(eval(n))
    case FoldNat(t) =>
      vlam("n", n => vlam("z", z => vlam("s", s => vfoldnat(eval(t), n, z, s))))

    case Bool           => VBool
    case True           => VTrue
    case False          => VFalse
    case If(t, c, a, b) => vif(eval(c), eval(t), eval(a), eval(b))

    case IntTy           => VInt
    case IntLit(v)       => VIntLit(v)
    case Binop(op, a, b) => vbinop(op, eval(a), eval(b))

    case Meta(id)              => vmeta(id)
    case InsertedMeta(id, bds) => vappbds(vmeta(id), bds)

  enum Unfold:
    case UnfoldMetas
    case UnfoldAll
  export Unfold.*

  def force(v: Val, unfold: Unfold = UnfoldAll): Val =
    v match
      case VFlex(id, sp) =>
        getMeta(id) match
          case Unsolved     => v
          case Solved(v, _) => force(vspine(v, sp), unfold)
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
      case SProj(sp, p) => Proj(quote(hd, sp, unfold), p)
      case SIf(sp, t, a, b) =>
        If(
          quote(t, unfold),
          quote(hd, sp, unfold),
          quote(a, unfold),
          quote(b, unfold)
        )
      case SBinop(a, op, b) => Binop(op, quote(hd, a, unfold), quote(b, unfold))

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
      case VFix(go, x, b, sp) =>
        quote(
          Fix(go, x, quote(b(VVar(k), VVar(k + 1)), unfold)(k + 2)),
          sp,
          unfold
        )

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

      case VSigma(x, t, u1, b, u2) =>
        Sigma(
          x,
          quote(t, unfold),
          quote(u1, unfold),
          quote(b, unfold),
          quote(u2, unfold)
        )
      case VPair(fst, snd) => Pair(quote(fst, unfold), quote(snd, unfold))

      case VLift(vf, v) => Lift(quote(vf, unfold), quote(v, unfold))
      case VQuote(v)    => Quote(quote(v, unfold))

      case VNat  => Nat
      case VZ    => Z
      case VS(n) => S(quote(n, unfold))

      case VBool  => Bool
      case VTrue  => True
      case VFalse => False

      case VInt       => IntTy
      case VIntLit(v) => IntLit(v)

  def nf(tm: Tm)(implicit env: Env = Nil): Tm = quote(eval(tm))(mkLvl(env.size))
