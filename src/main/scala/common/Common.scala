package common

object Common:
  def impossible(): Nothing = throw new Exception("impossible")

  type PosInfo = (Int, Int) // (line, col)

  // names
  case class Name(x: String):
    override def toString: String =
      if x.head.isLetter then x else s"($x)"

    def expose: String = x

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
  export Bind.*
