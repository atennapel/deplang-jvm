package core

import common.Common.*
import Syntax.*
import Value.*

object Evaluation:
  extension (c: Clos) def apply(v: Val): Val = eval(c.tm)(v :: c.env)

  def vapp(f: Val, a: Val): Val = f match
    case VLam(_, b)        => b(a)
    case VRigid(hd, sp)    => VRigid(hd, a :: sp)
    case VGlobal(x, sp, v) => VGlobal(x, a :: sp, () => vapp(f, v()))
    case _                 => impossible()

  def eval(tm: Tm)(implicit env: Env): Val = tm match
    case Local(ix)       => env(ix.expose)
    case Global(x)       => VGlobal(x, Nil, () => ???) // TODO
    case Let(_, _, v, b) => eval(b)(eval(v) :: env)

    case Type => VType

    case Pi(x, t, b) => VPi(x, eval(t), Clos(b))
    case Lam(x, b)   => VLam(x, Clos(b))
    case App(f, a)   => vapp(eval(f), eval(a))

  enum Unfold:
    case UnfoldNone
    case UnfoldAll
  export Unfold.*

  def force(v: Val, unfold: Unfold = UnfoldAll): Val = v match
    case VGlobal(_, _, v) if unfold == UnfoldAll => force(v(), UnfoldAll)
    case v                                       => v

  private def quote(hd: Tm, sp: Spine, unfold: Unfold)(implicit k: Lvl): Tm =
    sp match
      case Nil     => hd
      case a :: sp => App(quote(hd, sp, unfold), quote(a, unfold))

  private def quote(b: Clos, unfold: Unfold)(implicit k: Lvl): Tm =
    quote(b(VVar(k)), unfold)(k + 1)

  def quote(v: Val, unfold: Unfold = UnfoldNone)(implicit k: Lvl): Tm =
    force(v, unfold) match
      case VRigid(hd, sp)    => quote(Local(hd.toIx), sp, unfold)
      case VGlobal(x, sp, v) => quote(Global(x), sp, unfold)

      case VType => Type

      case VPi(x, t, b) => Pi(x, quote(t, unfold), quote(b, unfold))
      case VLam(x, b)   => Lam(x, quote(b, unfold))

  def nf(tm: Tm)(implicit env: Env = Nil): Tm = quote(eval(tm))(mkLvl(env.size))
