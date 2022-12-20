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
        "let",
        "in",
        "if",
        "then",
        "else",
        "fix"
      ),
      operators = Set(
        "=",
        ":=",
        "::=",
        ":",
        "\\",
        ".",
        ",",
        "->",
        "**",
        "^",
        "`",
        "$",
        "_"
      ),
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

    import LangLexer.{ident as ident0, userOp as userOp0, natural}
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
      ("^" *> atom).map(t => Lift(t)) <|>
        ("`" *> atom).map(t => Quote(t)) <|>
        ("$" *> atom).map(t => Splice(t)) <|>
        ("(" *> (userOp
          .map(Var.apply) <|> sepEndBy(tm, ",").map(mkPair)) <* ")") <|>
        holeP <|>
        natural.map(IntLit.apply) <|>
        ident.map(Var.apply)
    )

    private val unittype = Var(Name("UnitType"))
    private def mkPair(ts: List[Tm]): Tm = ts match
      case Nil => unittype
      case ts  => ts.reduceRight(Pair.apply)

    private val hole = Hole(None)

    lazy val tm: Parsley[Tm] = positioned(
      attempt(piSigma) <|> ifP <|> let <|> lam <|> fix <|>
        precedence[Tm](app)(
          Ops(InfixR)("**" #> ((l, r) => Sigma(DontBind, l, r))),
          Ops(InfixR)("->" #> ((l, r) => Pi(DontBind, Expl, l, r)))
        )
    )

    private lazy val piSigma: Parsley[Tm] =
      positioned(
        ((some(piParam) <|> app.map(t =>
          List((List(DontBind), Expl, Some(t)))
        )) <~> ("->" #> false <|> "**" #> true) <~> tm)
          .map { case ((ps, prod), rt) =>
            ps.foldRight(rt) { case ((xs, i, ty), rt) =>
              xs.foldRight(rt)((x, rt) =>
                if prod then Sigma(x, ty.getOrElse(hole), rt)
                else Pi(x, i, ty.getOrElse(hole), rt)
              )
            }
          }
      )

    private type PiParam = (List[Bind], Icit, Option[Ty])

    private lazy val piParam: Parsley[PiParam] =
      ("{" *> some(bind) <~> ":" *> tm <* "}").map((xs, ty) =>
        (xs, Impl, Some(ty))
      ) <|>
        ("(" *> some(bind) <~> ":" *> tm <* ")").map((xs, ty) =>
          (xs, Expl, Some(ty))
        )

    private lazy val let: Parsley[Tm] =
      positioned(
        ("let" *> identOrOp <~> option(
          ":" *> tm
        ) <~> ("=" #> Var(Name("U1")) <|> ":=" #> App(
          Var(Name("U0")),
          Var(Name("Fun")),
          Expl
        ) <|> "::=" #> App(Var(Name("U0")), Var(Name("Val")), Expl))
          <~> tm <~> "in" *> tm)
          .map { case ((((x, ty), univ), v), b) =>
            Let(x, univ, ty, v, b)
          }
      )

    private lazy val ifP: Parsley[Tm] =
      positioned(
        ("if" *> tm <~> "then" *> tm <~> "else" *> tm)
          .map { case ((c, t), f) => If(c, t, f) }
      )

    private lazy val lam: Parsley[Tm] =
      positioned(
        ("\\" *> many(lamParam) <~> "." *> tm).map((xs, b) =>
          xs.foldRight(b) { case ((x, i), b) => Lam(x, i, b) }
        )
      )

    private lazy val lamParam: Parsley[(Bind, Icit)] =
      ("{" *> bind <* "}").map(x => (x, Impl)) <|>
        bind.map(x => (x, Expl))

    private lazy val fix: Parsley[Tm] =
      positioned(
        ("fix" *> "(" *> identOrOp <~> identOrOp <~> "." *> tm <~> ")" *> atom)
          .map { case (((go, x), b), a) =>
            Fix(go, x, b, a)
          }
      )

    private lazy val app: Parsley[Tm] =
      precedence[Tm](appAtom)(
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

    private lazy val appAtom: Parsley[Tm] = positioned(
      (projAtom <~> many(arg) <~> option(let <|> lam <|> fix))
        .map { case ((fn, args), opt) =>
          (args ++ opt.map(t => (t, Expl))).foldLeft(fn) {
            case (fn, (arg, i)) =>
              App(fn, arg, i)
          }
        }
    )

    private lazy val arg: Parsley[(Tm, Icit)] =
      ("{" *> tm <* "}").map(t => (t, Impl)) <|>
        projAtom.map(t => (t, Expl))

    private lazy val projAtom: Parsley[Tm] = positioned(
      (atom <~> many(proj)).map((t, ps) => ps.foldLeft(t)(Proj.apply))
    )

    private lazy val proj: Parsley[ProjType] =
      ("." *> ("1" #> Fst <|> "2" #> Snd <|> identOrOp.map(Named.apply)))

    private def userOpStart(s: String): Parsley[String] =
      userOp0.filter(_.startsWith(s))
    private def opL(o: String): Parsley[InfixL.Op[Tm]] =
      attempt(userOpStart(o).filterNot(_.endsWith(":"))).map(op =>
        (l, r) => App(App(Var(Name(op)), l, Expl), r, Expl)
      )
    private def opR(o: String): Parsley[InfixR.Op[Tm]] =
      attempt(userOpStart(o)).map(op =>
        (l, r) => App(App(Var(Name(op)), l, Expl), r, Expl)
      )
    private def opP(o: String): Parsley[Prefix.Op[Tm]] =
      attempt(userOpStart(o)).map(op => t => App(Var(Name(op)), t, Expl))
    private def opLevel(s: String): List[Ops[Tm, Tm]] =
      val chars = s.toList
      List(
        Ops(Prefix)(chars.map(c => opP(c.toString))*),
        Ops(InfixL)(chars.map(c => opL(c.toString))*),
        Ops(InfixR)(chars.map(c => opR(c.toString))*)
      )
    private def ops(ss: String*): Seq[Ops[Tm, Tm]] =
      ss.map(opLevel).flatten

    // definitions
    lazy val defsP: Parsley[Defs] = sepEndBy(defP, ";").map(Defs.apply)

    private lazy val defP: Parsley[Def] =
      (identOrOp <~> option(
        ":" *> tm
      ) <~> ("=" #> Var(Name("U1")) <|> ":=" #> App(
        Var(Name("U0")),
        Var(Name("Fun")),
        Expl
      ) <|> "::=" #> App(Var(Name("U0")), Var(Name("Val")), Expl))
        <~> tm).map { case (((x, ot), univ), v) =>
        DDef(x, univ, ot, v)
      }

  lazy val parser: Parsley[Defs] = LangLexer.fully(TmParser.defsP)
