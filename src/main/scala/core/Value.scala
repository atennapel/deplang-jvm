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
  export Spine.*

  type VTy = Val
  enum Val:
    case VRigid(head: Lvl, spine: Spine)
    case VGlobal(name: Name, spine: Spine, value: () => Val)

    case VType(stage: Stage)

    case VPi(name: Bind, ty: VTy, stage: Stage, body: Clos)
    case VLam(name: Bind, body: Clos)

    case VLift(rep: Rep, tm: VTy)
    case VQuote(tm: Val)

    case VNat
    case VZ
    case VS(n: VTy)
  export Val.*

  private def name(x: String): Bind =
    if x == "_" then DontBind else DoBind(Name(x))
  def vlam(x: String, f: Val => Val): Val = VLam(name(x), CFun(f))
  def vpi(x: String, t: Val, st: Stage, f: Val => Val): Val =
    VPi(name(x), t, st, CFun(f))

  object VVar:
    def apply(lvl: Lvl) = VRigid(lvl, SId)
    def unapply(value: Val): Option[Lvl] = value match
      case VRigid(hd, SId) => Some(hd)
      case _               => None
