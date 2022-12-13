package surface

import common.Common.*
import core.Syntax.*
import core.Value.*
import core.Evaluation.{quote as quote0, eval as eval0}
import core.Pretty.{pretty as pretty0}
import core.Zonking.{zonk as zonk0}
import scala.annotation.tailrec

type Types = List[(Name, Lvl, VTy, VTy)]

final case class Ctx(
    lvl: Lvl,
    env: Env,
    types: Types,
    names: List[Name],
    bds: BDs,
    pos: PosInfo
):
  def enter(pos: PosInfo): Ctx = copy(pos = pos)

  def bind(x: Bind, ty: VTy, univ: VTy, inserted: Boolean = false): Ctx =
    x match
      case DoBind(y) if !inserted =>
        copy(
          lvl = lvl + 1,
          env = VVar(lvl) :: env,
          types = (y, lvl, ty, univ) :: types,
          names = x.toName :: names,
          bds = false :: bds
        )
      case _ =>
        copy(
          lvl = lvl + 1,
          env = VVar(lvl) :: env,
          names = x.toName :: names,
          bds = false :: bds
        )

  def define(x: Name, ty: VTy, univ: VTy, value: Val): Ctx =
    copy(
      lvl = lvl + 1,
      env = value :: env,
      types = (x, lvl, ty, univ) :: types,
      names = x :: names,
      bds = true :: bds
    )

  def lookup(x: Name): Option[(Ix, VTy, VTy)] =
    @tailrec
    def go(ts: Types): Option[(Ix, VTy, VTy)] = ts match
      case Nil                           => None
      case (y, k, ty, st) :: _ if x == y => Some((k.toIx(lvl), ty, st))
      case _ :: ts                       => go(ts)
    go(types)

  def eval(t: Tm): Val = eval0(t)(env)
  def quote(v: Val): Tm = quote0(v)(lvl)

  def zonk(t: Tm): Tm = zonk0(t)(lvl, env)
  def zonk(v: Val): Tm = zonk(quote(v))

  def pretty(t: Tm): String = pretty0(zonk(t))(names)
  def pretty(v: Val): String = pretty(zonk(v))

  def fresh(x: Bind): Bind = x.fresh(names)

object Ctx:
  def empty(pos: PosInfo): Ctx = Ctx(lvl0, Nil, Nil, Nil, Nil, pos)
