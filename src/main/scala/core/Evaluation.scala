package core

import common.Common.*
import Globals.getGlobal
import Syntax.*
import Value.*

object Evaluation:
  extension (c: Clos)
    def apply(v: Val): Val = c match
      case CClos(env, tm) => eval(tm)(v :: env)
      case CFun(f)        => f(v)

  def vapp(f: Val, a: Val): Val = f match
    case VLam(_, b)        => b(a)
    case VRigid(hd, sp)    => VRigid(hd, SApp(sp, a))
    case VGlobal(x, sp, v) => VGlobal(x, SApp(sp, a), () => vapp(v(), a))
    case _                 => impossible()

  def vquote(v: Val): Val = v match
    case VRigid(hd, SSplice(sp))     => VRigid(hd, sp)
    case VGlobal(hd, SSplice(sp), v) => VGlobal(hd, sp, () => vquote(v()))
    case v                           => VQuote(v)

  def vsplice(v: Val): Val = v match
    case VQuote(v)         => v
    case VRigid(hd, sp)    => VRigid(hd, SSplice(sp))
    case VGlobal(x, sp, v) => VGlobal(x, SSplice(sp), () => vsplice(v()))
    case _                 => impossible()

  def vfoldnat(t: VTy, n: Val, z: Val, s: Val): Val = n match
    case VZ => z
    // foldNat {t} (S n) z s ~> s n (foldNat {t} n z s)
    case VS(n)          => vapp(vapp(s, n), vfoldnat(t, n, z, s))
    case VRigid(hd, sp) => VRigid(hd, SFoldNat(sp, t, z, s))
    case VGlobal(x, sp, v) =>
      VGlobal(x, SFoldNat(sp, t, z, s), () => vfoldnat(t, v(), z, s))
    case _ => impossible()

  def eval(tm: Tm)(implicit env: Env): Val = tm match
    case Local(ix) => env(ix.expose)
    case Global(x) =>
      getGlobal(x) match
        case Some(e) =>
          val value = e.value
          VGlobal(x, SId, () => value)
        case None => impossible()
    case Let(_, _, _, v, b) => eval(b)(eval(v) :: env)

    case Type(s) => VType(s)

    case Pi(x, t, st, b) => VPi(x, eval(t), st, Clos(b))
    case Lam(x, b)       => VLam(x, Clos(b))
    case App(f, a)       => vapp(eval(f), eval(a))

    case Lift(rep, t) => VLift(rep, eval(t))
    case Quote(t)     => vquote(eval(t))
    case Splice(t)    => vsplice(eval(t))

    case Wk(t) => eval(t)(env.tail)

    case Nat  => VNat
    case Z    => VZ
    case S(n) => VS(eval(n))
    case FoldNat(t) =>
      vlam("n", n => vlam("z", z => vlam("s", s => vfoldnat(eval(t), n, z, s))))

  enum Unfold:
    case UnfoldNone
    case UnfoldAll
  export Unfold.*

  def force(v: Val, unfold: Unfold = UnfoldAll): Val =
    v match
      case VGlobal(_, _, v) if unfold == UnfoldAll => force(v(), UnfoldAll)
      case v                                       => v

  private def quote(hd: Tm, sp: Spine, unfold: Unfold)(implicit k: Lvl): Tm =
    sp match
      case SId         => hd
      case SApp(sp, a) => App(quote(hd, sp, unfold), quote(a, unfold))
      case SSplice(sp) => Splice(quote(hd, sp, unfold))
      case SFoldNat(sp, t, z, s) =>
        App(
          App(
            App(FoldNat(quote(t, unfold)), quote(hd, sp, unfold)),
            quote(z, unfold)
          ),
          quote(s, unfold)
        )

  private def quote(b: Clos, unfold: Unfold)(implicit k: Lvl): Tm =
    quote(b(VVar(k)), unfold)(k + 1)

  def quote(v: Val, unfold: Unfold = UnfoldNone)(implicit k: Lvl): Tm =
    force(v, unfold) match
      case VRigid(hd, sp)    => quote(Local(hd.toIx), sp, unfold)
      case VGlobal(x, sp, v) => quote(Global(x), sp, unfold)

      case VType(s) => Type(s)

      case VPi(x, t, st, b) => Pi(x, quote(t, unfold), st, quote(b, unfold))
      case VLam(x, b)       => Lam(x, quote(b, unfold))

      case VLift(rep, v) => Lift(rep, quote(v, unfold))
      case VQuote(v)     => Quote(quote(v, unfold))

      case VNat  => Nat
      case VZ    => Z
      case VS(n) => S(quote(n, unfold))

  def nf(tm: Tm)(implicit env: Env = Nil): Tm = quote(eval(tm))(mkLvl(env.size))
