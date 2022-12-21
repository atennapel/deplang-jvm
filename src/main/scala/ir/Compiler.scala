package ir

import common.Common.*
import common.Ref
import Syntax.*
import jvmir.Syntax as IR

import scala.collection.mutable

/*
 * 1. eta expansion of definitions
 * 2. closure conversion
 * 3. lambda lift
 */
object Compiler:
  def compile(ds: Defs): IR.Defs = IR.Defs(ds.toList.flatMap(go))

  // normalize def name based on jvm limitations
  private def norm(x: Name): Name =
    Name(
      (if x.isOperator then "f" else "") +
        x.expose
          .replace(".", "$_DOT_$")
          .replace(";", "$_SEMICOLON_$")
          .replace("[", "$_BRACKET_$")
          .replace("/", "$_SLASH_$")
          .replace("<", "$_ANGLELEFT_$")
          .replace(">", "$_ANGLERIGHT_$")
          .replace(":", "$_COLON_$")
    )

  private def go(d: Def): List[IR.Def] = d match
    case DData(x, ps, cs) =>
      List(IR.DData(norm(x), cs.map((c, as) => (norm(c), as.map(go)))))
    case DDef(x, t, v) =>
      val (ps, rt, b) = etaExpand(t, v)
      implicit val name: Name = norm(x)
      implicit val args: Args = ps.zipWithIndex.map { case ((x, _), ix) =>
        x -> ix
      }.toMap
      implicit val newDefs: NewDefs = mutable.ArrayBuffer.empty
      implicit val uniq: Ref[Int] = Ref(0)
      val newdef =
        IR.DDef(name, false, ps.map((_, t) => go(t)), go(t.retrn), go(b, true))
      newDefs.toList ++ List(newdef)

  private type Args = Map[Int, Int]
  private type NewDefs = mutable.ArrayBuffer[IR.Def]

  private def go(
      t: Tm,
      tr: Boolean
  )(implicit
      name: Name,
      args: Args,
      defs: NewDefs,
      uniq: Ref[Int]
  ): IR.Tm =
    t match
      case Local(x, t) =>
        args.get(x) match
          case Some(ix) => IR.Arg(ix, goTy(t))
          case None     => IR.Local(x, goTy(t))
      case Global(x, t) =>
        if t.params.nonEmpty then impossible()
        IR.Global(norm(x), false, go(t), Nil)
      case Let(x, TDef(Nil, t), v, b) =>
        IR.Let(x, go(t), go(v, false), go(b, tr)(name, args - x, defs, uniq))

      case Let(x, t, v, b) =>
        val g = lambdaLift(uniq.updateGetOld(_ + 1), t, v)
        go(b.subst(Map(x -> g)), tr)
      case Lam(x, t1, t2, b) =>
        val g = lambdaLift(uniq.updateGetOld(_ + 1), TDef(t1, t2), t)
        go(g, tr)

      case Fix(g, x, t1, t2, b, arg) =>
        val glb = fixLift(uniq.updateGetOld(_ + 1), g, x, t1, t2, b)
        go(App(glb, arg), true)

      case App(f0, a) =>
        val (f, as) = t.flattenApps
        f match
          case Global(x, t) =>
            if t.params.size != as.size then impossible()
            IR.Global(
              norm(x),
              if x == name then tr else false,
              go(t),
              as.map(go(_, false))
            )
          case Fix(g, x, t1, t2, b, arg) =>
            val glb = fixLift(uniq.updateGetOld(_ + 1), g, x, t1, t2, b)
            go(glb.apps(arg :: as), true)
          case _ => impossible()

      case Pair(t1, t2, fst, snd) =>
        IR.Pair(box(t1, go(fst, false)), box(t2, go(snd, false)))
      case Fst(ty, t) => unbox(ty, IR.Fst(go(t, false)))
      case Snd(ty, t) => unbox(ty, IR.Snd(go(t, false)))

      case True  => IR.True
      case False => IR.False

      case IntLit(n)       => IR.IntLit(n)
      case Binop(op, a, b) => IR.Binop(op, go(a, false), go(b, false))

      case If(TDef(Nil, t), c, a, b) =>
        IR.If(go(t), go(c, false), go(a, true), go(b, true))

      case Con(x, t, as) =>
        IR.Con(
          norm(x),
          go(t),
          as.map((a, b, p) =>
            if p then (box(b, go(a, false)), go(b), p)
            else (go(a, false), go(b), p)
          )
        )

      case _ => impossible()

  private def box(ty: Ty, tm: IR.Tm): IR.Tm = ty match
    case TPair(_, _) => tm
    case TCon(_, _)  => tm
    case TPoly       => tm
    case _ =>
      val ct = go(ty)
      tm match
        case IR.Unbox(_, tm) => tm
        case IR.Box(_, tm)   => tm
        case _               => IR.Box(ct, tm)

  private def unbox(ty: Ty, tm: IR.Tm): IR.Tm = ty match
    case TPair(_, _) => tm
    case TCon(_, _)  => tm
    case TPoly       => tm
    case _ =>
      val ct = go(ty)
      tm match
        case IR.Unbox(_, tm) => tm
        case IR.Box(_, tm)   => tm
        case _               => IR.Unbox(ct, tm)

  private def go(t: Ty): IR.Ty = t match
    case TBool       => IR.TBool
    case TInt        => IR.TInt
    case TPair(_, _) => IR.TPair
    case TCon(x, _)  => IR.TCon(norm(x))
    case TPoly       => IR.TObject

  private def go(t: TDef): IR.TDef = t match
    case TDef(ps, rt) => IR.TDef(ps.map(go), go(rt))

  private def goTy(t: TDef): IR.Ty = t match
    case TDef(Nil, rt) => go(rt)
    case _             => impossible()

  private def eta(
      t: TDef,
      ps: List[(Int, Ty)],
      scope: Set[Int] = Set.empty
  ): List[(Int, Ty)] =
    (t, ps) match
      case (TDef(Nil, rt), Nil) => Nil
      case (TDef(t :: ts, rt), Nil) =>
        val y = if scope.isEmpty then 0 else scope.max + 1
        val rest = eta(TDef(ts, rt), Nil, scope + y)
        (y, t) :: rest
      case (TDef(t1 :: ts, rt), (x, t2) :: rest) if t1 == t2 =>
        eta(TDef(ts, rt), rest, scope + x)
      case _ => impossible()

  private def etaExpand(t: TDef, v: Tm): (List[(Int, Ty)], Ty, Tm) =
    val (ps, rt, b) = v.flattenLams
    val mps = eta(t, ps)
    val nps = ps ++ mps
    val nb = b.apps(mps.map((x, t) => Local(x, TDef(t))))
    (nps, t.retrn, nb)

  private def lambdaLift(x: Int, t: TDef, v: Tm)(implicit
      name: Name,
      defs: NewDefs
  ): Tm =
    val (ps, rt, d) = etaExpand(t, v)
    val fv = v.freeVars
      .map((x, t) => {
        if t.params.nonEmpty then impossible()
        x -> t.retrn
      })
      .distinctBy((y, _) => y)
    val nps = fv ++ ps
    val vv = d.lams(nps, TDef(rt))
    val newname = Name(s"$name$$$x")
    val args = nps.zipWithIndex.map { case ((x, _), ix) =>
      x -> ix
    }.toMap
    val newdef = IR.DDef(
      newname,
      true,
      nps.map((_, t) => go(t)),
      go(rt),
      go(d, true)(newname, args, defs, Ref(0))
    )
    defs += newdef
    Global(newname, TDef(nps.map(_._2), rt))
      .apps(fv.map((x, t) => Local(x, TDef(t))))

  private def fixLift(x: Int, g: Int, y: Int, t1: Ty, t: TDef, v: Tm)(implicit
      name: Name,
      defs: NewDefs
  ): Tm =
    val (ps, rt, d) = etaExpand(t, v)
    val fv = v.freeVars
      .filterNot((z, _) => z == g || z == y)
      .map((x, t) => {
        if t.params.nonEmpty then impossible()
        x -> t.retrn
      })
      .distinctBy((y, _) => y)
    val nps = fv ++ List((y, t1)) ++ ps
    val vv = d.lams(nps, TDef(rt))
    val newname = Name(s"$name$$$x")
    val args = nps.zipWithIndex.map { case ((x, _), ix) =>
      x -> ix
    }.toMap
    val gl = Global(newname, TDef(nps.map(_._2), rt))
      .apps(fv.map((x, t) => Local(x, TDef(t))))
    val d2 = d.subst(Map(g -> gl))
    val newdef = IR.DDef(
      newname,
      true,
      nps.map((_, t) => go(t)),
      go(rt),
      go(d2, true)(newname, args, defs, Ref(0))
    )
    defs += newdef
    gl
