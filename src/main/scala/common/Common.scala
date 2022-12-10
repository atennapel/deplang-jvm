package common

import scala.annotation.targetName

object Common:
  def impossible(): Nothing = throw new Exception("impossible")

  type PosInfo = (Int, Int) // (line, col)

  // debruijn indeces
  opaque type Ix = Int
  inline def ix0: Ix = 0
  inline def mkIx(i: Int): Ix = i
  extension (i: Ix)
    inline def expose: Int = i
    inline def +(o: Int): Ix = i + o

  // levels
  opaque type Lvl = Int
  inline def lvl0: Lvl = 0
  inline def mkLvl(i: Int): Lvl = i
  extension (l: Lvl)
    @targetName("addLvl")
    inline def +(o: Int): Lvl = l + o
    inline def -(o: Int): Lvl = l - o
    @targetName("exposeLvl")
    inline def expose: Int = l
    inline def toIx(implicit k: Lvl): Ix = k - l - 1

  // names
  case class Name(x: String):
    override def toString: String =
      if x.head.isLetter then x else s"($x)"

    def expose: String = x

    def fresh(implicit ns: List[Name]): Name =
      if ns.contains(this) then Name(s"${x}'").fresh else this

  enum Bind:
    case DontBind
    case DoBind(name: Name)

    override def toString: String = this match
      case DontBind  => "_"
      case DoBind(x) => x.toString

    def toName: Name = this match
      case DontBind  => Name("_")
      case DoBind(x) => x

    def toSet: Set[Name] = this match
      case DontBind  => Set.empty
      case DoBind(x) => Set(x)

    def fresh(implicit ns: List[Name]): Bind = this match
      case DoBind(x) => DoBind(x.fresh)
      case DontBind  => DontBind
  export Bind.*

  // stages
  enum Rep:
    case RVal
    case RFun
    case RErased

    override def toString: String = this match
      case RVal    => "Val"
      case RFun    => "Fun"
      case RErased => "Erased"
  export Rep.*

  enum Stage:
    case S0(rep: Rep)
    case S1

    def split[A](s0: Rep => A, s1: A): A = this match
      case S1      => s1
      case S0(rep) => s0(rep)
  export Stage.*
