package core

import common.Common.*
import common.Debug.debug
import Value.*
import Evaluation.*

object Unification:
  final case class UnifyError(msg: String) extends Exception(msg)

  private def unify(a: Spine, b: Spine)(implicit k: Lvl): Unit = (a, b) match
    case (SId, SId)                     => ()
    case (SApp(sp1, a1), SApp(sp2, a2)) => unify(sp1, sp2); unify(a1, a2)
    case (SSplice(sp1), SSplice(sp2))   => unify(sp1, sp2)
    case _                              => throw UnifyError("spine mismatch")

  private def unify(a: Clos, b: Clos)(implicit k: Lvl): Unit =
    val v = VVar(k); unify(a(v), b(v))

  def unify(a: Val, b: Val)(implicit k: Lvl): Unit =
    debug(s"unify ${quote(a)} ~ ${quote(b)}")
    (force(a, UnfoldNone), force(b, UnfoldNone)) match
      case (VType(s1), VType(s2)) if s1 == s2 => ()
      case (VNat, VNat)                       => ()
      case (VZ, VZ)                           => ()
      case (VS(n), VS(m))                     => unify(n, m)
      case (VLift(_, a), VLift(_, b))         => unify(a, b)
      case (VQuote(a), VQuote(b))             => unify(a, b)
      case (VPi(_, t1, _, b1), VPi(_, t2, _, b2)) =>
        unify(t1, t2); unify(b1, b2)
      case (VRigid(h1, sp1), VRigid(h2, sp2)) if h1 == h2 => unify(sp1, sp2)

      case (VLam(_, b1), VLam(_, b2)) => unify(b1, b2)
      case (VLam(_, b), f) => val v = VVar(k); unify(b(v), vapp(f, v))(k + 1)
      case (f, VLam(_, b)) => val v = VVar(k); unify(vapp(f, v), b(v))(k + 1)

      case (VGlobal(x1, sp1, v1), VGlobal(x2, sp2, v2)) if x1 == x2 =>
        try unify(sp1, sp2)
        catch case _: UnifyError => unify(v1(), v2())
      case (VGlobal(_, _, v1), VGlobal(_, _, v2)) => unify(v1(), v2())
      case (VGlobal(_, _, v1), v2)                => unify(v1(), v2)
      case (v1, VGlobal(_, _, v2))                => unify(v1, v2())

      case _ => throw UnifyError(s"failed to unify ${quote(a)} ~ ${quote(b)}")
