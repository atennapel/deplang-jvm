package core

import common.Common.*
import Syntax.*

object Pretty:
  private def prettyPi(tm: Tm)(implicit ns: List[Name]): String = tm match
    case Pi(DontBind, Expl, t, _, b, _) =>
      s"${prettyParen(t, true)} -> ${prettyPi(b)(DontBind.toName :: ns)}"
    case Pi(DoBind(x0), Expl, t, _, b, _) =>
      val x = x0.fresh
      s"($x : ${pretty(t)}) -> ${prettyPi(b)(x :: ns)}"
    case Pi(x0, Impl, t, _, b, _) =>
      val x = x0.fresh
      s"{$x : ${pretty(t)}} -> ${prettyPi(b)(x.toName :: ns)}"
    case rest => pretty(rest)

  private def prettySigma(tm: Tm)(implicit ns: List[Name]): String = tm match
    case Sigma(DontBind, t, _, b, _) =>
      s"${prettyParen(t, true)} ** ${prettySigma(b)(DontBind.toName :: ns)}"
    case Sigma(DoBind(x0), t, _, b, _) =>
      val x = x0.fresh
      s"($x : ${pretty(t)}) ** ${prettySigma(b)(x :: ns)}"
    case rest => pretty(rest)

  private def prettyLam(tm: Tm)(implicit ns: List[Name]): String =
    def go(tm: Tm, ns: List[Name], first: Boolean = false): String = tm match
      case Lam(x0, Expl, b) =>
        val x = x0.fresh
        s"${if first then "" else " "}$x${go(b, x.toName :: ns)}"
      case Lam(x0, Impl, b) =>
        val x = x0.fresh
        s"${if first then "" else " "}{$x}${go(b, x.toName :: ns)}"
      case rest => s". ${pretty(rest)(ns)}"
    s"\\${go(tm, ns, true)}"

  private def prettyApp(tm: Tm)(implicit ns: List[Name]): String = tm match
    case App(f, a, Expl) => s"${prettyApp(f)} ${prettyParen(a)}"
    case App(f, a, Impl) => s"${prettyApp(f)} {${pretty(a)}}"
    case f               => prettyParen(f)

  private def prettyParen(tm: Tm, app: Boolean = false)(implicit
      ns: List[Name]
  ): String = tm match
    case Local(_)            => pretty(tm)
    case Global(_)           => pretty(tm)
    case VF                  => pretty(tm)
    case VFVal               => pretty(tm)
    case VFFun               => pretty(tm)
    case U0                  => pretty(tm)
    case U1                  => pretty(tm)
    case App(_, _, _) if app => pretty(tm)
    case Lift(_, _)          => pretty(tm)
    case Quote(_)            => pretty(tm)
    case Splice(_)           => pretty(tm)
    case Bool                => pretty(tm)
    case True                => pretty(tm)
    case False               => pretty(tm)
    case IntTy               => pretty(tm)
    case IntLit(v)           => pretty(tm)
    case Pair(_, _)          => pretty(tm)
    case Proj(_, _)          => pretty(tm)
    case Meta(_)             => pretty(tm)
    case InsertedMeta(_, _)  => pretty(tm)
    case TCon(x, Nil)        => pretty(tm)
    case Con(x, _, Nil)      => pretty(tm)
    case Wk(t)               => prettyParen(t, app)(ns.tail)
    case _                   => s"(${pretty(tm)})"

  private def flattenPair(tm: Tm): List[Tm] = tm match
    case Pair(fst, snd) => fst :: flattenPair(snd)
    case tm             => List(tm)

  def pretty(tm: Tm)(implicit ns: List[Name]): String = tm match
    case Local(ix) => s"${ns(ix.expose)}"
    case Global(x) => s"$x"
    case Let(x0, u, t, v, b) =>
      val x = x0.fresh
      val s = u match
        case App(U0, VFVal, Expl) => "::"
        case App(U0, VFFun, Expl) => ":"
        case U1                   => ""
        case _                    => "?"
      s"let $x : ${pretty(t)} $s= ${pretty(v)} in ${pretty(b)(x :: ns)}"

    case VF    => "VF"
    case VFVal => "Val"
    case VFFun => "Fun"
    case U0    => "U0"
    case U1    => "U1"

    case Pi(_, _, _, _, _, _) => prettyPi(tm)
    case Lam(_, _, _)         => prettyLam(tm)
    case App(_, _, _)         => prettyApp(tm)
    case Fix(go0, x0, b, arg) =>
      val go = go0.fresh
      val x = x0.fresh(go :: ns)
      s"fix ($go $x. ${pretty(b)(x :: go :: ns)}) ${prettyParen(arg)}"

    case Sigma(_, _, _, _, _) => prettySigma(tm)
    case Proj(tm, proj)       => s"${prettyParen(tm)}$proj"
    case Pair(_, _) =>
      val es = flattenPair(tm)
      s"(${es.map(pretty).mkString(", ")})"

    case Lift(_, t) => s"^${prettyParen(t)}"
    case Quote(t)   => s"`${prettyParen(t)}"
    case Splice(t)  => s"$$${prettyParen(t)}"

    case Wk(t) => pretty(t)(ns.tail)

    case Bool  => "Bool"
    case True  => "True"
    case False => "False"
    case If(_, c, a, b) =>
      s"if ${pretty(c)} then ${pretty(a)} else ${pretty(b)}"

    case IntTy           => "Int"
    case IntLit(v)       => s"$v"
    case Binop(op, a, b) => s"$a $op $b"

    case TCon(x, Nil) => s"$x"
    case TCon(x, as)  => s"$x ${as.map(prettyParen(_)).mkString(" ")}"

    case Con(x, _, Nil) => s"$x"
    case Con(x, _, as) =>
      s"$x ${as.map((t, _, _) => prettyParen(t)).mkString(" ")}"
    case Case(x, _, _, cs) =>
      s"case ${prettyParen(x)} | ${cs
          .map((c, xs, b) => {
            val (ys, ns2) = enter(xs.map(_._1))
            s"$c ${ys.mkString(" ")} => ${pretty(b)(ns2)}"
          })
          .mkString(" | ")}"

    case Meta(id)            => s"?$id"
    case InsertedMeta(id, _) => s"?$id"

  private def enter(xs: List[Bind])(implicit
      ns: List[Name]
  ): (List[Bind], List[Name]) =
    def go(xs: List[Bind], ns: List[Name]): (List[Bind], List[Name]) = xs match
      case Nil => (Nil, ns)
      case x :: xs =>
        val y = x.fresh(ns)
        val (ys, ns2) = go(xs, y.toName :: ns)
        (y :: ys, ns2)
    go(xs, ns)

  def pretty(d: Def)(implicit ns: List[Name]): String = d match
    case DDef(x0, u, t, v) =>
      val x = x0.fresh
      val s = u match
        case App(U0, VFVal, Expl) => "::"
        case App(U0, VFFun, Expl) => ":"
        case U1                   => ""
        case _                    => "?"
      s"$x : ${pretty(t)} $s= ${pretty(v)(x :: ns)};"
    case DData(x, ps, cs) =>
      s"data $x${if ps.isEmpty then "" else s" ${ps.mkString(" ")}"} := ${cs
          .map((x, ts) =>
            s"$x${
                if ts.isEmpty then ""
                else s" ${ts.map(prettyParen(_)(ps.reverse ++ (x :: ns))).mkString(" ")}"
              }"
          )
          .mkString(" | ")};"

  def pretty(ds: Defs)(implicit ns: List[Name]): String =
    ds.toList.map(pretty).mkString("\n")
