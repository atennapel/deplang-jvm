package surface

import common.Common.*
import core.Syntax.*
import core.Value.*
import core.Evaluation.{quote as quote0, eval as eval0}
import core.Pretty.{pretty as pretty0}
import scala.annotation.tailrec

type Types = List[(Name, Lvl, VTy, Stage)]

final case class Ctx(
    lvl: Lvl,
    env: Env,
    types: Types,
    names: List[Name],
    pos: PosInfo
):
  def enter(pos: PosInfo): Ctx = copy(pos = pos)

  def bind(x: Bind, ty: VTy, st: Stage): Ctx = x match
    case DontBind =>
      copy(lvl = lvl + 1, env = VVar(lvl) :: env, names = x.toName :: names)
    case DoBind(y) =>
      copy(
        lvl = lvl + 1,
        env = VVar(lvl) :: env,
        types = (y, lvl, ty, st) :: types,
        names = x.toName :: names
      )

  def define(x: Name, ty: VTy, st: Stage, value: Val): Ctx =
    copy(
      lvl = lvl + 1,
      env = value :: env,
      types = (x, lvl, ty, st) :: types,
      names = x :: names
    )

  def lookup(x: Name): Option[(Ix, VTy, Stage)] =
    @tailrec
    def go(ts: Types): Option[(Ix, VTy, Stage)] = ts match
      case Nil                           => None
      case (y, k, ty, st) :: _ if x == y => Some((k.toIx(lvl), ty, st))
      case _ :: ts                       => go(ts)
    go(types)

  def eval(t: Tm): Val = eval0(t)(env)
  def quote(v: Val): Tm = quote0(v)(lvl)

  def pretty(t: Tm): String = pretty0(t)(names)
  def pretty(v: Val): String = pretty(quote(v))

  def fresh(x: Bind): Bind = x.fresh(names)

object Ctx:
  def empty(pos: PosInfo): Ctx = Ctx(lvl0, Nil, Nil, Nil, pos)
