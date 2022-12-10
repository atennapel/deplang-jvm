package core

import common.Common.*
import common.Debug.debug
import Syntax.*
import Globals.getGlobal

object Staging:
  private enum Env:
    case Empty
    case Def0(env: Env, value: Val0)
    case Def1(env: Env, value: Val1)

    def tail: Env = this match
      case Def0(e, _) => e
      case Def1(e, _) => e
      case _          => impossible()
  import Env.*

  private enum Val1:
    case VLam1(body: Val1 => Val1)
    case VQuote(tm: Val0)
    case VType1
  import Val1.*

  private enum Val0:
    case VVar0(lvl: Lvl)
    case VGlobal0(name: Name)
    case VApp0(fn: Val0, arg: Val0)
    case VPi0(name: Bind, rep: Rep, ty: Val0, body: Val0 => Val0)
    case VLam0(name: Bind, body: Val0 => Val0)
    case VLet0(name: Name, rep: Rep, ty: Val0, value: Val0, body: Val0 => Val0)
    case VType0(rep: Rep)
    case VNat0
    case VZ0
    case VS0(n: Val0)
  import Val0.*

  private def vvar1(ix: Ix)(implicit env: Env): Val1 =
    def go(env: Env, i: Int): Val1 = (env, i) match
      case (Def1(_, v), 0) => v
      case (Def1(e, _), i) => go(e, i - 1)
      case (Def0(e, _), i) => go(e, i - 1)
      case _               => impossible()
    go(env, ix.expose)

  private def vapp1(f: Val1, a: Val1): Val1 = f match
    case VLam1(f) => f(a)
    case _        => impossible()

  private def eval1Bind(t: Tm, u: Val1)(implicit env: Env): Val1 =
    eval1(t)(Def1(env, u))

  private def eval1(t: Tm)(implicit env: Env): Val1 = t match
    case Local(ix)          => vvar1(ix)
    case Global(x)          => eval1(getGlobal(x).get.tm)
    case Let(_, _, _, v, b) => eval1(b)(Def1(env, eval1(v)))

    case Type(s) => VType1

    case Pi(x, t, st, b) => VType1
    case Lam(x, b)       => VLam1(v => eval1Bind(b, v))
    case App(f, a)       => vapp1(eval1(f), eval1(a))

    case Lift(rep, t) => VType1
    case Quote(t)     => VQuote(eval0(t))
    case Splice(t)    => impossible()

    case Wk(t) => eval1(t)(env.tail)

    case Nat  => impossible()
    case Z    => impossible()
    case S(_) => impossible()

  private def vvar0(ix: Ix)(implicit env: Env): Val0 =
    def go(env: Env, i: Int): Val0 = (env, i) match
      case (Def0(_, v), 0) => v
      case (Def0(e, _), i) => go(e, i - 1)
      case (Def1(e, _), i) => go(e, i - 1)
      case _               => impossible()
    go(env, ix.expose)

  private def vsplice(v: Val1): Val0 = v match
    case VQuote(v) => v
    case _         => impossible()

  private def eval0Bind(t: Tm, u: Val0)(implicit env: Env): Val0 =
    eval0(t)(Def0(env, u))

  private def eval0(t: Tm)(implicit env: Env): Val0 = t match
    case Local(ix) => vvar0(ix)
    case Global(x) => VGlobal0(x)
    case Let(x, S0(rep), t, v, b) =>
      VLet0(x, rep, eval0(t), eval0(v), v => eval0Bind(b, v))
    case Let(_, _, _, _, _) => impossible()

    case Type(S0(rep)) => VType0(rep)
    case Type(S1)      => impossible()

    case Pi(x, t, S0(rep), b) => VPi0(x, rep, eval0(t), v => eval0Bind(b, v))
    case Pi(_, _, _, _)       => impossible()
    case Lam(x, b)            => VLam0(x, v => eval0Bind(b, v))
    case App(f, a)            => VApp0(eval0(f), eval0(a))

    case Lift(rep, t) => impossible()
    case Quote(t)     => impossible()
    case Splice(t)    => vsplice(eval1(t))

    case Wk(t) => eval0(t)(env.tail)

    case Nat  => VNat0
    case Z    => VZ0
    case S(n) => VS0(eval0(n))

  private def quote0(v: Val0)(implicit k: Lvl): Tm = v match
    case VVar0(l)    => Local(l.toIx)
    case VGlobal0(x) => Global(x)
    case VApp0(f, a) => App(quote0(f), quote0(a))
    case VPi0(x, rep, t, b) =>
      Pi(x, quote0(t), S0(rep), quote0(b(VVar0(k)))(k + 1))
    case VLam0(x, b) => Lam(x, quote0(b(VVar0(k)))(k + 1))
    case VLet0(x, rep, t, v, b) =>
      Let(x, S0(rep), quote0(t), quote0(v), quote0(b(VVar0(k)))(k + 1))
    case VType0(rep)  => Type(S0(rep))
    case VNat0        => Nat
    case VZ0          => Z
    case VS0(n: Val0) => S(quote0(n))

  private def stage(tm: Tm): Tm =
    debug(s"stage $tm")
    quote0(eval0(tm)(Empty))(lvl0)

  private def stage(d: Def): Option[Def] = d match
    case DDef(x, st @ S0(_), t, v) => Some(DDef(x, st, stage(t), stage(v)))
    case _                         => None

  def stage(ds: Defs): Defs = Defs(ds.toList.flatMap(stage))
