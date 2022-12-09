import common.Debug.setDebug
import surface.Parser.parser
import surface.Elaboration.elaborate

import java.io.File
import scala.io.Source
import parsley.io.given

object Main:
  @main def run(filename0: String) =
    setDebug(true)
    var filename = filename0
    if !filename.endsWith(".lang") then filename = s"$filename0.lang"
    val moduleName = filename.dropRight(5)
    val ds = parser.parseFromFile(new File(filename)).flatMap(_.toTry).get
    println(ds)
    val cds = elaborate(ds)
    println(cds)
