package core

import common.Common.*
import Syntax.Tm

object Value:
  type Env = List[Val]

  final case class Clos(env: Env, tm: Tm)
  object Clos:
    def apply(tm: Tm)(implicit env: Env): Clos = Clos(env, tm)

  type Spine = List[Val]

  type VTy = Val
  enum Val:
    case VRigid(head: Lvl, spine: Spine)
    case VGlobal(name: Name, spine: Spine, value: () => Val)

    case VType

    case VPi(name: Bind, ty: VTy, body: Clos)
    case VLam(name: Bind, body: Clos)
  export Val.*

  object VVar:
    def apply(lvl: Lvl) = VRigid(lvl, Nil)
    def unapply(value: Val): Option[Lvl] = value match
      case VRigid(hd, Nil) => Some(hd)
      case _               => None
