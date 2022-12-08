package surface

import common.Common.*
import Syntax.*

import parsley.Parsley, Parsley._
import scala.language.implicitConversions

object Parser:
  object LangLexer:
    import parsley.token.{LanguageDef, Lexer, Predicate, Parser}
    import parsley.character.{alphaNum, isWhitespace, char, oneOf}
    import parsley.combinator.{eof, many}

    private val userOps = "`~!@$%^&*-+=|:/?><,."
    private val userOpsTail = s"${userOps}#_;"
    private val uriCharsHead = "-_~:/?#@!$&'*+,%="
    private val uriChars = "-_~:/?#@!$&'*+,%="

    val lang = LanguageDef.plain.copy(
      commentLine = "--",
      commentStart = "{-",
      commentEnd = "-}",
      nestedComments = true,
      keywords = Set(
        "Type",
        "let",
        "in",
        "def"
      ),
      operators = Set("=", ":", "\\", ".", "->"),
      identStart = Predicate(_.isLetter),
      identLetter =
        Predicate(c => c.isLetterOrDigit || c == '_' || c == '\'' || c == '-'),
      opStart = Predicate(userOps.contains(_)),
      opLetter = Predicate(userOpsTail.contains(_)),
      space = Predicate(isWhitespace)
    )
    val lexer = new Lexer(lang)

    def fully[A](p: => Parsley[A]): Parsley[A] = lexer.whiteSpace *> p <* eof

    val ident: Parsley[String] = lexer.identifier
    val userOp: Parsley[String] = lexer.userOp
    val natural: Parsley[Int] = lexer.natural

    def keyword(s: String): Parsley[Unit] = lexer.keyword(s)
    def symbol(s: String): Parsley[Unit] = void(lexer.symbol_(s))

    object Implicits:
      given Conversion[String, Parsley[Unit]] with
        def apply(s: String): Parsley[Unit] =
          if lang.keywords(s) then lexer.keyword(s)
          else if lang.operators(s) then lexer.maxOp(s)
          else void(lexer.symbol_(s))

  object TmParser:
    import parsley.expr.{precedence, Ops, InfixL, InfixR, Prefix, Postfix}
    import parsley.combinator.{many, some, option, sepEndBy}
    import parsley.Parsley.pos

    import LangLexer.{ident as ident0, userOp as userOp0, natural, uri}
    import LangLexer.Implicits.given

    private def positioned(p: => Parsley[Tm]): Parsley[Tm] =
      (pos <~> p).map(Pos.apply)

    private lazy val ident: Parsley[Name] = ident0.map(Name.apply)
    private lazy val userOp: Parsley[Name] = userOp0.map(Name.apply)
    private lazy val identOrOp: Parsley[Name] = ("(" *> userOp <* ")") <|> ident

    private lazy val bind: Parsley[Bind] =
      "_" #> DontBind <|> identOrOp.map(DoBind.apply)

    private lazy val holeP: Parsley[Tm] =
      ("_" *> option(ident)).map(x => x.fold(hole)(x => Hole(Some(x))))

    private lazy val atom: Parsley[Tm] = positioned(
      ("(" *> (userOp.map(Var.apply) <|> tm) <* ")") <|>
        holeP <|>
        "Type" #> Type <|>
        nat <|>
        ident.map(Var.apply)
    )

    private val hole = Hole(None)

    private val nZ = Var(Name("Z"))
    private val nS = Var(Name("S"))
    private lazy val nat: Parsley[Tm] = natural.map(n =>
      var c: Tm = nZ
      for (_ <- 0.until(n)) c = App(nS, c)
      c
    )

    lazy val tm: Parsley[Tm] = positioned(
      attempt(pi) <|> let <|> lam <|>
        precedence[Tm](app)(
          Ops(InfixR)("->" #> ((l, r) => Pi(DontBind, l, r)))
        )
    )

    private lazy val pi: Parsley[Tm] =
      ((some(piParam) <|> app.map(t =>
        List(Right((List(DontBind), Expl, Some(t))))
      )) <~> "->" *> tm)
        .map { case (ps, rt) =>
          ps.foldRight(rt) {
            case (Right((xs, i, ty)), rt) =>
              xs.foldRight(rt)((x, rt) =>
                if isSigma then RSigma(x, ty.getOrElse(hole), rt)
                else RPi(x, i, ty.getOrElse(hole), rt)
              )
            case (Left(xs), rt) =>
              xs.foldRight(rt)(RPiLvl(_, _))
          }
        }

    private type PiSigmaParam = (List[Bind], Option[Ty])

    private lazy val piSigmaParam: Parsley[PiSigmaParam] =
      ("<" *> some(bind) <* ">").map(Left.apply) <|>
        attempt("{{" *> some(bind) <~> option(":" *> tm) <* "}}").map(
          (xs, ty) => Right((xs, Impl(Inst), ty))
        ) <|>
        ("{" *> some(bind) <~> option(":" *> tm) <* "}").map((xs, ty) =>
          Right((xs, Impl(Unif), ty))
        ) <|>
        attempt("(" *> some(bind) <~> ":" *> tm <* ")").map((xs, ty) =>
          Right((xs, Expl, Some(ty)))
        ) <|> ("(" <~> ")").map(_ =>
          Right((List(DontBind), Expl, Some(unittype)))
        )

    private val ifVar: RTm = RVar(Name("if_"))
    private val ifIndVar: RTm = RVar(Name("if-ind_"))
    private lazy val ifTm: Parsley[RTm] =
      ("if" *> tm <~> option(":" *> tm) <~> "then" *> tm <~> "else" *> tm)
        .map { case (((c, ty), t), f) =>
          RApp(
            RApp(
              RApp(
                ty.map(RApp(ifIndVar, _, RArgIcit(Expl))).getOrElse(ifVar),
                c,
                RArgIcit(Expl)
              ),
              t,
              RArgIcit(Expl)
            ),
            f,
            RArgIcit(Expl)
          )
        }

    private lazy val let: Parsley[RTm] =
      ("let" *> identOrOp <~> many(defParam) <~>
        option(":" *> tm) <~> "=" *> tm <~> ";" *> tm).map {
        case ((((x, ps), ty), v), b) =>
          RLet(
            x,
            ty.map(typeFromParams(ps, _)),
            lamFromDefParams(ps, v, ty.isEmpty),
            b
          )
      }

    private lazy val open: Parsley[RTm] =
      ("open" *> projAtom <~> option(
        "(" *> sepEndBy(openPart, ",") <* ")"
      ) <~> option(
        "hiding" *> "(" *> sepEndBy(identOrOp, ",") <* ")"
      ) <~> ";" *> tm).map { case (((tm, ns), hiding), b) =>
        ROpen(tm, ns, hiding.getOrElse(Nil), b)
      }
    private lazy val openPart: Parsley[(Name, Option[Name])] =
      identOrOp <~> option("=" *> identOrOp)

    private lazy val exportP: Parsley[RTm] =
      ("export" *> option("(" *> sepEndBy(openPart, ",") <* ")") <~> option(
        "hiding" *> "(" *> sepEndBy(identOrOp, ",") <* ")"
      )).map { case (ns, hiding) => RExport(ns, hiding.getOrElse(Nil)) }

    private lazy val sig: Parsley[RTm] =
      ("sig" *> many(defParam) <~> "{" *> sepEndBy(sigDecl, ";") <* "}")
        .map { case (ps, ds) =>
          val ps2 = ps.flatMap {
            case Left(xs)            => xs.map(x => (x, None))
            case Right((xs, i, oty)) => xs.map(x => (x, Some((i, oty))))
          }
          RSig(ps2, ds)
        }

    private lazy val sigDecl: Parsley[SigDecl] =
      (option("export") <~> "open" *> projAtom <~> option(
        "(" *> sepEndBy(openPart, ",") <* ")"
      ) <~> option(
        "hiding" *> "(" *> sepEndBy(identOrOp, ",") <* ")"
      )).map { case (((exp, tm), ns), hiding) =>
        SOpen(exp.isDefined, tm, ns, hiding.getOrElse(Nil))
      } <|>
        attempt(
          (option("private") <~> identOrOp <~> many(defParam) <~> option(
            ":" *> tm
          ) <~> "=" *> tm).map { case ((((p, x), ds), ty), b) =>
            SDef(
              p.isDefined,
              x,
              ty.map(typeFromParams(ds, _)),
              lamFromDefParams(ds, b, ty.isEmpty)
            )
          }
        ) <|>
        (identOrOp <~> many(defParam) <~> option(":" *> tm)).map {
          case ((x, ds), ty) => SLet(x, ty.map(typeFromParams(ds, _)))
        }

    private lazy val mod: Parsley[RTm] =
      ("mod" *> many(defParam) <~> "{" *> sepEndBy(modDecl, ";") <* "}")
        .map { case (ps, ds) =>
          val ps2 = ps.flatMap {
            case Left(xs)            => xs.map(x => (x, None))
            case Right((xs, i, oty)) => xs.map(x => (x, Some((i, oty))))
          }
          RMod(ps2, ds)
        }

    private lazy val modDecl: Parsley[ModDecl] =
      (option("export") <~> "open" *> projAtom <~> option(
        "(" *> sepEndBy(openPart, ",") <* ")"
      ) <~> option(
        "hiding" *> "(" *> sepEndBy(identOrOp, ",") <* ")"
      )).map { case (((exp, tm), ns), hiding) =>
        DOpen(exp.isDefined, tm, ns, hiding.getOrElse(Nil))
      } <|>
        (option("private") <~> identOrOp <~> many(defParam) <~> option(
          ":" *> tm
        ) <~> "=" *> tm).map { case ((((p, x), ds), ty), b) =>
          DLet(
            p.isDefined,
            x,
            ty.map(typeFromParams(ds, _)),
            lamFromDefParams(ds, b, ty.isEmpty)
          )
        }

    private lazy val lam: Parsley[RTm] =
      ("\\" *> many(lamParam) <~> "." *> tm).map(lamFromLamParams(_, _))

    private type LamParam =
      Either[(List[Bind], Option[Name]), (List[Bind], RArgInfo, Option[RTy])]
    private lazy val lamParam: Parsley[LamParam] =
      attempt("<" *> some(bind) <~> "=" *> identOrOp <* ">").map((xs, i) =>
        Left((xs, Some(i)))
      ) <|>
        attempt(
          "{{" *> some(bind) <~> option(":" *> tm) <~> "=" *> identOrOp <* "}}"
        ).map { case ((xs, ty), y) => Right((xs, RArgNamed(y, Inst), ty)) } <|>
        attempt(
          "{" *> some(bind) <~> option(":" *> tm) <~> "=" *> identOrOp <* "}"
        ).map { case ((xs, ty), y) => Right((xs, RArgNamed(y, Unif), ty)) } <|>
        attempt(piSigmaParam).map {
          case Right((xs, i, ty)) =>
            Right((xs, RArgIcit(i), ty))
          case Left(xs) => Left((xs, None))
        } <|>
        bind.map(x => Right((List(x), RArgIcit(Expl), None)))

    private type DefParam = Either[List[Bind], (List[Bind], Icit, Option[RTy])]
    private lazy val defParam: Parsley[DefParam] =
      attempt(piSigmaParam) <|> bind.map(x => Right((List(x), Expl, None)))

    private lazy val app: Parsley[RTm] =
      precedence[RTm](appAtom)(
        ops(
          "`@#?,.",
          "*/%",
          "+-",
          ":",
          "=!",
          "<>",
          "&",
          "^",
          "|",
          "$",
          "~"
        )*
      )

    private lazy val appAtom: Parsley[RTm] = positioned(
      (projAtom <~> many(arg) <~> option(let <|> open <|> mod <|> sig <|> lam))
        .map { case ((fn, args), opt) =>
          (args.flatten ++ opt.map(t => Right((t, RArgIcit(Expl)))))
            .foldLeft(fn) { case (fn, e) =>
              e.fold(
                (arg, i) => RAppLvl(fn, arg, i),
                (arg, i) => RApp(fn, arg, i)
              )
            }
        }
    )

    private type Arg = Either[(RLevel, Option[Name]), (RTm, RArgInfo)]

    private lazy val arg: Parsley[List[Arg]] =
      attempt("<" *> some(identOrOp) <~> "=" *> level <* ">").map((xs, l) =>
        xs.map(x => Left((l, Some(x))))
      ) <|>
        ("<" *> level <* ">").map(l => List(Left((l, None)))) <|>
        attempt("{{" *> some(identOrOp) <~> "=" *> tm <* "}}").map((xs, t) =>
          xs.map(x => Right((t, RArgNamed(x, Inst))))
        ) <|>
        attempt("{{" *> tm <* "}}").map(t =>
          List(Right((t, RArgIcit(Impl(Inst)))))
        ) <|>
        attempt("{" *> some(identOrOp) <~> "=" *> tm <* "}").map((xs, t) =>
          xs.map(x => Right((t, RArgNamed(x, Unif))))
        ) <|>
        ("{" *> tm <* "}").map(t => List(Right((t, RArgIcit(Impl(Unif)))))) <|>
        projAtom.map(t => List(Right((t, RArgIcit(Expl)))))

    private lazy val projAtom: Parsley[RTm] =
      positioned(
        (atom <~> many(proj)).map((t, ps) => ps.foldLeft(t)(RProj.apply))
      )

    private lazy val proj: Parsley[RProjType] =
      ("." *> ("1" #> RFst <|> "2" #> RSnd <|> identOrOp.map(RNamed.apply)))

    private def typeFromParams(ps: List[DefParam], rt: RTy): RTy =
      ps.foldRight(rt)((x, b) =>
        x match
          case Right((xs, i, ty)) =>
            xs.foldRight(b)(RPi(_, i, ty.getOrElse(hole), _))
          case Left(xs) =>
            xs.foldRight(b)(RPiLvl(_, _))
      )

    private def lamFromDefParams(
        ps: List[DefParam],
        b: RTm,
        useTypes: Boolean
    ): RTm =
      ps.foldRight(b)((x, b) =>
        x match
          case Right((xs, i, ty)) =>
            xs.foldRight(b)(
              RLam(
                _,
                RArgIcit(i),
                if useTypes then Some(ty.getOrElse(hole)) else None,
                _
              )
            )
          case Left(xs) => xs.foldRight(b)(RLamLvl(_, None, _))
      )
    private def lamFromLamParams(ps: List[LamParam], b: RTm): RTm =
      ps.foldRight(b)((x, b) =>
        x match
          case Right((xs, i, ty)) =>
            xs.foldRight(b)(
              RLam(_, i, ty, _)
            )
          case Left((xs, i)) => xs.foldRight(b)(RLamLvl(_, i, _))
      )

    private def userOpStart(s: String): Parsley[String] =
      userOp0.filter(_.startsWith(s))
    private def opL(o: String): Parsley[InfixL.Op[RTm]] =
      attempt(userOpStart(o).filterNot(_.endsWith(":"))).map(op =>
        (l, r) =>
          RApp(RApp(RVar(Name(op)), l, RArgIcit(Expl)), r, RArgIcit(Expl))
      )
    private def opR(o: String): Parsley[InfixR.Op[RTm]] =
      attempt(userOpStart(o)).map(op =>
        (l, r) =>
          RApp(RApp(RVar(Name(op)), l, RArgIcit(Expl)), r, RArgIcit(Expl))
      )
    private def opP(o: String): Parsley[Prefix.Op[RTm]] =
      attempt(userOpStart(o)).map(op =>
        t => RApp(RVar(Name(op)), t, RArgIcit(Expl))
      )
    private def opLevel(s: String): List[Ops[RTm, RTm]] =
      val chars = s.toList
      List(
        Ops(Prefix)(chars.map(c => opP(c.toString))*),
        Ops(InfixL)(chars.map(c => opL(c.toString))*),
        Ops(InfixR)(chars.map(c => opR(c.toString))*)
      )
    private def ops(ss: String*): Seq[Ops[RTm, RTm]] =
      ss.map(opLevel).flatten

  lazy val parser: Parsley[RTm] = LangLexer.fully(TmParser.tm)
