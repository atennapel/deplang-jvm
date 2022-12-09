package surface

import common.Common.*
import core.Syntax.*
import core.Value.*
import core.Evaluation.{quote as quote0, eval as eval0}
import scala.annotation.tailrec

type Types = List[(Name, Lvl, VTy)]

final case class Ctx(
    lvl: Lvl,
    env: Env,
    types: Types,
    pos: PosInfo
):
  def enter(pos: PosInfo): Ctx = copy(pos = pos)

  def bind(x: Bind, ty: VTy): Ctx = x match
    case DontBind => copy(lvl = lvl + 1, env = VVar(lvl) :: env)
    case DoBind(x) =>
      copy(lvl = lvl + 1, env = VVar(lvl) :: env, types = (x, lvl, ty) :: types)

  def define(x: Name, ty: VTy, value: Val): Ctx =
    copy(lvl = lvl + 1, env = value :: env, types = (x, lvl, ty) :: types)

  def lookup(x: Name): Option[(Ix, VTy)] =
    @tailrec
    def go(ts: Types): Option[(Ix, VTy)] = ts match
      case Nil                       => None
      case (y, k, ty) :: _ if x == y => Some((k.toIx(lvl), ty))
      case _ :: ts                   => go(ts)
    go(types)

  def eval(t: Tm): Val = eval0(t)(env)
  def quote(v: Val): Tm = quote0(v)(lvl)

object Ctx:
  def empty(pos: PosInfo): Ctx = Ctx(lvl0, Nil, Nil, pos)
