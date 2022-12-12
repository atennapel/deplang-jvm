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
    case SApp(spine: Spine, arg: Val)
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
    case VGlobal(name: Name, spine: Spine, value: () => Val)

    case VVF
    case VVFVal
    case VVFFun
    case VU1

    case VPi(name: Bind, ty: VTy, body: Clos)
    case VFun(left: VTy, vf: VTy, right: VTy)
    case VLam(name: Bind, body: Clos)

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
  def vlam(x: String, f: Val => Val): Val = VLam(name(x), CFun(f))
  def vpi(x: String, t: Val, f: Val => Val): Val =
    VPi(name(x), t, CFun(f))

  object VVar:
    def apply(lvl: Lvl) = VRigid(HVar(lvl), SId)
    def unapply(value: Val): Option[Lvl] = value match
      case VRigid(HVar(hd), SId) => Some(hd)
      case _                     => None

  object VU0:
    def apply() = VRigid(HU0, SId)
    def unapply(value: Val): Boolean = value match
      case VRigid(HU0, SId) => true
      case _                => false

  object VU:
    def apply(vf: VTy) = VRigid(HU0, SApp(SId, vf))
    def unapply(value: Val): Option[VTy] = value match
      case VRigid(HU0, SApp(SId, vf)) => Some(vf)
      case _                          => None

  object VUVal:
    def apply() = VRigid(HU0, SApp(SId, VVFVal))
    def unapply(value: Val): Boolean = value match
      case VRigid(HU0, SApp(SId, VVFVal)) => true
      case _                              => false

  object VUFun:
    def apply() = VRigid(HU0, SApp(SId, VVFFun))
    def unapply(value: Val): Boolean = value match
      case VRigid(HU0, SApp(SId, VVFFun)) => true
      case _                              => false
