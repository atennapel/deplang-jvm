package core

import common.Common.*
import Syntax.Tm

object Value:
  type Env = List[Val]

  final case class Clos(env: Env, tm: Tm)
  object Clos:
    def apply(tm: Tm)(implicit env: Env): Clos = Clos(env, tm)

  enum Spine:
    case SId
    case SApp(spine: Spine, arg: Val)
    case SSplice(spine: Spine)
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

  object VVar:
    def apply(lvl: Lvl) = VRigid(lvl, SId)
    def unapply(value: Val): Option[Lvl] = value match
      case VRigid(hd, SId) => Some(hd)
      case _               => None
