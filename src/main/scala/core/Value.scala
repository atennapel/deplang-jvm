package core

import common.Common.*
import Syntax.Tm

object Value:
  type Env = List[Val]

  enum Clos:
    case CClos(env: Env, tm: Tm)
    case CFun(fn: Val => Val)
  export Clos.*
  object Clos:
    def apply(tm: Tm)(implicit env: Env): Clos = CClos(env, tm)

  enum Spine:
    case SId
    case SApp(spine: Spine, arg: Val, icit: Icit)
    case SSplice(spine: Spine)
    case SFoldNat(spine: Spine, ty: VTy, z: Val, s: Val)
    case SFst(spine: Spine)
    case SSnd(spine: Spine)
  export Spine.*

  enum Head:
    case HVar(lvl: Lvl)
    case HU0
  export Head.*

  type VTy = Val
  enum Val:
    case VRigid(head: Head, spine: Spine)
    case VFlex(id: MetaId, spine: Spine)
    case VGlobal(name: Name, spine: Spine, value: () => Val)

    case VVF
    case VVFVal
    case VVFFun
    case VU1

    case VPi(name: Bind, icit: Icit, ty: VTy, u1: VTy, body: Clos, u2: VTy)
    case VLam(name: Bind, icit: Icit, body: Clos)

    case VPairTy(fst: VTy, snd: VTy)
    case VPair(fst: Val, snd: Val)

    case VLift(vf: VTy, tm: VTy)
    case VQuote(tm: Val)

    case VNat
    case VZ
    case VS(n: VTy)
  export Val.*

  private def name(x: String): Bind =
    if x == "_" then DontBind else DoBind(Name(x))
  def vlam(x: String, f: Val => Val): Val = VLam(name(x), Expl, CFun(f))
  def vpi(x: String, t: Val, u1: VTy, u2: VTy, f: Val => Val): Val =
    VPi(name(x), Expl, t, u1, CFun(f), u2)

  object VVar:
    def apply(lvl: Lvl) = VRigid(HVar(lvl), SId)
    def unapply(value: Val): Option[Lvl] = value match
      case VRigid(HVar(hd), SId) => Some(hd)
      case _                     => None

  object VMeta:
    def apply(id: MetaId) = VFlex(id, SId)
    def unapply(value: Val): Option[MetaId] = value match
      case VFlex(id, SId) => Some(id)
      case _              => None

  object VU0:
    def apply() = VRigid(HU0, SId)
    def unapply(value: Val): Boolean = value match
      case VRigid(HU0, SId) => true
      case _                => false

  object VU:
    def apply(vf: VTy) = VRigid(HU0, SApp(SId, vf, Expl))
    def unapply(value: Val): Option[VTy] = value match
      case VRigid(HU0, SApp(SId, vf, Expl)) => Some(vf)
      case _                                => None

  object VUVal:
    def apply() = VRigid(HU0, SApp(SId, VVFVal, Expl))
    def unapply(value: Val): Boolean = value match
      case VRigid(HU0, SApp(SId, VVFVal, Expl)) => true
      case _                                    => false

  object VUFun:
    def apply() = VRigid(HU0, SApp(SId, VVFFun, Expl))
    def unapply(value: Val): Boolean = value match
      case VRigid(HU0, SApp(SId, VVFFun, Expl)) => true
      case _                                    => false
