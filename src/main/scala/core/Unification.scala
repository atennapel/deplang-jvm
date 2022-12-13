package core

import common.Common.*
import common.Debug.debug
import Value.*
import Evaluation.*
import Syntax.*
import Metas.*

import scala.collection.immutable.IntMap

object Unification:
  final case class UnifyError(msg: String) extends Exception(msg)

  private final case class PRen(dom: Lvl, cod: Lvl, ren: IntMap[Lvl]):
    def lift: PRen = PRen(dom + 1, cod + 1, ren + (cod.expose -> dom))

  private def invert(sp: Spine)(implicit k: Lvl): PRen =
    def go(sp: Spine): (Lvl, IntMap[Lvl]) = sp match
      case SId => (lvl0, IntMap.empty)
      case SApp(sp, t, i) =>
        val (dom, ren) = go(sp)
        force(t) match
          case VVar(x) if !ren.contains(x.expose) =>
            (dom + 1, ren + (x.expose -> dom))
          case _ => throw UnifyError(s"non-var in meta spine")
      case _ => throw UnifyError(s"eliminator in meta spine")
    val (dom, ren) = go(sp)
    PRen(dom, k, ren)

  private def rename(m: MetaId, v: Val)(implicit pren: PRen): Tm =
    def goSp(hd: Tm, sp: Spine)(implicit pren: PRen): Tm = sp match
      case SId            => hd
      case SApp(sp, a, i) => App(goSp(hd, sp), go(a), i)
      case SSplice(sp)    => Splice(goSp(hd, sp))
      case SFoldNat(sp, t, z, s) =>
        App(
          App(App(FoldNat(go(t)), goSp(hd, sp), Expl), go(z), Expl),
          go(s),
          Expl
        )
      case SFst(sp) => Fst(goSp(hd, sp))
      case SSnd(sp) => Snd(goSp(hd, sp))

    def goCl(c: Clos)(implicit pren: PRen): Tm =
      go(c(VVar(pren.cod)))(pren.lift)

    def go(t: Val)(implicit pren: PRen): Tm = force(t, UnfoldMetas) match
      case VFlex(hd, sp) if m == hd =>
        throw UnifyError(s"occurs check failed: $m")
      case VFlex(hd, sp) => goSp(Meta(hd), sp)

      case VRigid(HU0, sp) => goSp(U0, sp)
      case VRigid(HVar(x), sp) =>
        pren.ren.get(x.expose) match
          case None     => throw UnifyError(s"escaped variable: '$x")
          case Some(x2) => goSp(Local(pren.dom.toIx(x2)), sp)

      case VGlobal(x, sp, v) => goSp(Global(x), sp)

      case VVF    => VF
      case VVFVal => VFVal
      case VVFFun => VFFun
      case VU0()  => U0
      case VU1    => U1

      case VPi(x, i, t, u1, b, u2) =>
        Pi(
          x,
          i,
          go(t),
          go(u1),
          goCl(b),
          go(u2)
        )
      case VLam(x, i, b) => Lam(x, i, goCl(b))

      case VPairTy(fst, snd) => PairTy(go(fst), go(snd))
      case VPair(fst, snd)   => Pair(go(fst), go(snd))

      case VLift(vf, v) => Lift(go(vf), go(v))
      case VQuote(v)    => Quote(go(v))

      case VNat  => Nat
      case VZ    => Z
      case VS(n) => S(go(n))

    go(v)

  private def lams(sp: Spine, b: Tm): Tm =
    def icits(sp: Spine): List[Icit] = sp match
      case SId            => Nil
      case SApp(sp, _, i) => i :: icits(sp)
      case _              => impossible()
    def go(x: Int, is: List[Icit]): Tm = is match
      case Nil     => b
      case i :: is => Lam(DoBind(Name(s"x$x")), i, go(x + 1, is))
    go(0, icits(sp).reverse)

  private def solve(id: MetaId, sp: Spine, v: Val)(implicit k: Lvl): Unit =
    debug(s"solve ?$id := ${quote(v)}")
    implicit val pren: PRen = invert(sp)
    val rhs = rename(id, v)
    val solution = lams(sp, rhs)
    debug(s"solution ?$id = $solution")
    solveMeta(id, eval(solution)(Nil), solution)

  private def unify(a: Spine, b: Spine)(implicit k: Lvl): Unit = (a, b) match
    case (SId, SId)                           => ()
    case (SApp(sp1, a1, _), SApp(sp2, a2, _)) => unify(sp1, sp2); unify(a1, a2)
    case (SSplice(sp1), SSplice(sp2))         => unify(sp1, sp2)
    case (SFoldNat(sp1, t1, z1, s1), SFoldNat(sp2, t2, z2, s2)) =>
      unify(sp1, sp2); unify(t1, t2); unify(z1, z2); unify(s1, s2)
    case (SFst(sp1), SFst(sp2)) => unify(sp1, sp2)
    case (SSnd(sp1), SSnd(sp2)) => unify(sp1, sp2)
    case _                      => throw UnifyError("spine mismatch")

  private def unify(a: Clos, b: Clos)(implicit k: Lvl): Unit =
    val v = VVar(k); unify(a(v), b(v))

  def unify(a: Val, b: Val)(implicit k: Lvl): Unit =
    debug(s"unify ${quote(a)} ~ ${quote(b)}")
    (force(a, UnfoldMetas), force(b, UnfoldMetas)) match
      case (VVF, VVF)                 => ()
      case (VVFVal, VVFVal)           => ()
      case (VVFFun, VVFFun)           => ()
      case (VU1, VU1)                 => ()
      case (VNat, VNat)               => ()
      case (VZ, VZ)                   => ()
      case (VS(n), VS(m))             => unify(n, m)
      case (VLift(_, a), VLift(_, b)) => unify(a, b)
      case (VQuote(a), VQuote(b))     => unify(a, b)
      case (VPi(_, _, t1, u11, b1, u12), VPi(_, _, t2, u21, b2, u22)) =>
        unify(t1, t2); unify(u11, u21); unify(b1, b2); unify(u12, u22)
      case (VPair(a1, b1), VPair(a2, b2))     => unify(a1, a2); unify(b1, b2)
      case (VPairTy(a1, b1), VPairTy(a2, b2)) => unify(a1, a2); unify(b1, b2)
      case (VRigid(h1, sp1), VRigid(h2, sp2)) if h1 == h2 => unify(sp1, sp2)

      case (VLam(_, i1, b1), VLam(_, i2, b2)) if i1 == i2 => unify(b1, b2)
      case (VLam(_, i, b), f) =>
        val v = VVar(k); unify(b(v), vapp(f, v, i))(k + 1)
      case (f, VLam(_, i, b)) =>
        val v = VVar(k); unify(vapp(f, v, i), b(v))(k + 1)

      case (VFlex(id1, sp1), VFlex(id2, sp2)) if id1 == id2 => unify(sp1, sp2)
      case (VFlex(id, sp), v)                               => solve(id, sp, v)
      case (v, VFlex(id, sp))                               => solve(id, sp, v)

      case (VGlobal(x1, sp1, v1), VGlobal(x2, sp2, v2)) if x1 == x2 =>
        try unify(sp1, sp2)
        catch case _: UnifyError => unify(v1(), v2())
      case (VGlobal(_, _, v1), VGlobal(_, _, v2)) => unify(v1(), v2())
      case (VGlobal(_, _, v1), v2)                => unify(v1(), v2)
      case (v1, VGlobal(_, _, v2))                => unify(v1, v2())

      case _ => throw UnifyError(s"failed to unify ${quote(a)} ~ ${quote(b)}")
