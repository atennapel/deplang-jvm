import surface.Parser.parser

import java.io.File
import scala.io.Source
import parsley.io.given

object Main:
  @main def run(filename0: String) =
    var filename = filename0
    if !filename.endsWith(".lang") then filename = s"$filename0.lang"
    val moduleName = filename.dropRight(5)
    val ds = parser.parseFromFile(new File(filename)).flatMap(_.toTry).get
    println(ds)
