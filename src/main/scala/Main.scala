import surface.Parser.parser
import surface.Elaboration.elaborate
import core.Pretty.pretty
import core.Staging.stage
import common.Debug.setDebug
import ir.Simplifier.simplify
import ir.Compiler.compile
import jvmir.Generator.generate

import java.io.File
import scala.io.Source
import parsley.io.given

object Main:
  @main def run(filename0: String) =
    setDebug(true)
    var filename = filename0
    if !filename.endsWith(".lang") then filename = s"$filename0.lang"
    val moduleName = filename.dropRight(5).split("/").last
    val ds = parser.parseFromFile(new File(filename)).flatMap(_.toTry).get
    val cds = elaborate(ds)
    println("elaborate:")
    println(pretty(cds)(Nil))
    println("stage:")
    val sds = stage(cds)
    println(sds)
    println("simplify:")
    val simp = simplify(sds)
    println(simp)
    println("compile to jvm ir:")
    val jvmir = compile(simp)
    println(jvmir)
    println("generate JVM bytecode")
    generate(moduleName, jvmir)
