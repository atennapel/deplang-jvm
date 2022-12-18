package jvmir

import common.Common.*
import Syntax.*

import org.objectweb.asm.*
import org.objectweb.asm.Opcodes.*
import org.objectweb.asm.commons.*

import scala.collection.mutable
import scala.collection.immutable.IntMap

import java.util.function.Function
import java.lang.invoke.LambdaMetafactory
import java.lang.reflect.Modifier
import java.lang.invoke.MethodType
import java.lang.invoke.MethodHandles

import java.io.BufferedOutputStream
import java.io.FileOutputStream

object Generator:
  private final case class Ctx(moduleName: String, moduleType: Type)

  def generate(moduleName: String, ds: Defs): Unit =
    implicit val cw: ClassWriter = new ClassWriter(
      ClassWriter.COMPUTE_MAXS + ClassWriter.COMPUTE_FRAMES
    )
    cw.visit(V1_8, ACC_PUBLIC, moduleName, null, "java/lang/Object", null)

    implicit val ctx: Ctx = Ctx(moduleName, Type.getType(s"L$moduleName;"))

    // empty constructor
    val con = cw.visitMethod(ACC_PRIVATE, "<init>", "()V", null, null)
    con.visitVarInsn(ALOAD, 0)
    con.visitMethodInsn(
      INVOKESPECIAL,
      "java/lang/Object",
      "<init>",
      "()V",
      false
    )
    con.visitInsn(RETURN)
    con.visitMaxs(1, 1)
    con.visitEnd()

    // main method
    val m = new Method(
      "main",
      Type.VOID_TYPE,
      List(Type.getType("[Ljava/lang/String;")).toArray
    )
    val main: GeneratorAdapter =
      new GeneratorAdapter(ACC_PUBLIC + ACC_STATIC, m, null, null, cw)
    main.visitFieldInsn(
      GETSTATIC,
      "java/lang/System",
      "out",
      "Ljava/io/PrintStream;"
    )
    main.push(0)
    main.invokeStatic(
      ctx.moduleType,
      new Method("main", Type.INT_TYPE, List(Type.INT_TYPE).toArray)
    )
    main.invokeStatic(
      Type.getType(classOf[Integer]),
      Method.getMethod("Integer valueOf (int)")
    )
    main.invokeVirtual(
      Type.getType(classOf[Object]),
      Method.getMethod("String toString ()")
    )
    main.visitMethodInsn(
      INVOKEVIRTUAL,
      "java/io/PrintStream",
      "println",
      "(Ljava/lang/String;)V",
      false
    )
    main.visitInsn(RETURN)
    main.visitMaxs(3, 1)
    main.visitEnd

    // generate definitions
    ds.toList.foreach(gen)

    // generate static block
    genStaticBlock(ds)

    // end
    cw.visitEnd()
    val bos = new BufferedOutputStream(
      new FileOutputStream(s"$moduleName.class")
    )
    bos.write(cw.toByteArray())
    bos.close()

  private val PAIR_TYPE: Type = Type.getType("Ljvmstd/Pair;")
  private val OBJECT_TYPE: Type = Type.getType("Ljava/lang/Object;")

  private def gen(t: Ty): Type = t match
    case TBool => Type.BOOLEAN_TYPE
    case TInt  => Type.INT_TYPE
    case TPair => PAIR_TYPE

  private def constantValue(e: Tm): Option[Any] = e match
    case True      => Some(true)
    case False     => Some(false)
    case IntLit(n) => Some(n)
    case _         => None

  private type Locals = IntMap[Int]

  private def genStaticBlock(
      ds0: Defs
  )(implicit ctx: Ctx, cw: ClassWriter): Unit =
    val ds = ds0.toList.filter {
      case DDef(x, _, Nil, rt, b) if constantValue(b).isEmpty => true
      case _                                                  => false
    }
    if ds.nonEmpty then
      val m = new Method("<clinit>", Type.VOID_TYPE, Nil.toArray)
      implicit val mg: GeneratorAdapter =
        new GeneratorAdapter(ACC_STATIC, m, null, null, cw)
      implicit val locals: Locals = IntMap.empty
      ds.foreach(d => {
        d match
          case DDef(x, g, Nil, rt, b) =>
            gen(b)
            mg.putStatic(ctx.moduleType, x.expose, gen(rt))
          case _ =>
      })
      mg.visitInsn(RETURN)
      mg.endMethod()

  private def gen(d: Def)(implicit cw: ClassWriter, ctx: Ctx): Unit = d match
    case DDef(x, g, Nil, rt, v) =>
      cw.visitField(
        (if g then ACC_PRIVATE + ACC_SYNTHETIC
         else ACC_PUBLIC) + ACC_FINAL + ACC_STATIC,
        x.expose,
        gen(rt).getDescriptor,
        null,
        constantValue(v).orNull
      )
    case DDef(x, g, ps, rt, v) =>
      val m = new Method(
        x.toString,
        gen(rt),
        ps.map(gen).toList.toArray
      )
      implicit val mg: GeneratorAdapter =
        new GeneratorAdapter(
          (if g then ACC_PRIVATE + ACC_SYNTHETIC else ACC_PUBLIC) + ACC_STATIC,
          m,
          null,
          null,
          cw
        )
      implicit val locals: Locals = IntMap.empty
      gen(v)
      mg.returnValue()
      mg.endMethod()

  private def gen(
      t: Tm
  )(implicit mg: GeneratorAdapter, ctx: Ctx, locals: Locals): Unit =
    t match
      case Arg(ix, ty) => mg.loadArg(ix)

      case Global(x, TDef(Nil, rt), Nil) =>
        mg.getStatic(ctx.moduleType, x.expose, gen(rt))
      case Global(x, TDef(ps, rt), as) =>
        if ps.size != as.size then impossible()
        as.foreach(gen)
        mg.invokeStatic(
          ctx.moduleType,
          new Method(x.expose, gen(rt), ps.map(gen).toArray)
        )

      case Local(x, ty) => mg.loadLocal(locals(x))
      case Let(x, ty, v, b) =>
        val vr = mg.newLocal(gen(ty))
        gen(v)
        mg.storeLocal(vr)
        gen(b)(mg, ctx, locals + (x -> vr))

      case Pair(fst, snd) =>
        mg.newInstance(PAIR_TYPE)
        mg.dup()
        gen(fst)
        gen(snd)
        mg.invokeConstructor(
          PAIR_TYPE,
          new Method(
            "<init>",
            Type.VOID_TYPE,
            List(OBJECT_TYPE, OBJECT_TYPE).toArray
          )
        )
      case Fst(tm)       => gen(tm); mg.getField(PAIR_TYPE, "fst", OBJECT_TYPE)
      case Snd(tm)       => gen(tm); mg.getField(PAIR_TYPE, "snd", OBJECT_TYPE)
      case Box(ty, tm)   => gen(tm); box(ty)
      case Unbox(ty, tm) => gen(tm); mg.unbox(gen(ty))

      case True  => mg.push(true)
      case False => mg.push(false)
      case If(t, c, a, b) =>
        val lFalse = new Label
        val lEnd = new Label
        gen(c)
        mg.visitJumpInsn(IFEQ, lFalse)
        gen(a)
        mg.visitJumpInsn(GOTO, lEnd)
        mg.visitLabel(lFalse)
        gen(b)
        mg.visitLabel(lEnd)

      case IntLit(n) => mg.push(n)
      case Binop(op, a, b) =>
        gen(a)
        gen(b)
        op match
          case OAdd => mg.visitInsn(IADD)
          case OMul => mg.visitInsn(IMUL)
          case OSub => mg.visitInsn(ISUB)
          case ODiv => mg.visitInsn(IDIV)
          case OMod => mg.visitInsn(IREM)
          case OEq =>
            val skip = mg.newLabel()
            val end = mg.newLabel()
            mg.ifICmp(GeneratorAdapter.EQ, skip)
            mg.push(false)
            mg.visitJumpInsn(GOTO, end)
            mg.visitLabel(skip)
            mg.push(true)
            mg.visitLabel(end)
          case ONeq =>
            val skip = mg.newLabel()
            val end = mg.newLabel()
            mg.ifICmp(GeneratorAdapter.NE, skip)
            mg.push(false)
            mg.visitJumpInsn(GOTO, end)
            mg.visitLabel(skip)
            mg.push(true)
            mg.visitLabel(end)
          case OLt =>
            val skip = mg.newLabel()
            val end = mg.newLabel()
            mg.ifICmp(GeneratorAdapter.LT, skip)
            mg.push(false)
            mg.visitJumpInsn(GOTO, end)
            mg.visitLabel(skip)
            mg.push(true)
            mg.visitLabel(end)
          case OGt =>
            val skip = mg.newLabel()
            val end = mg.newLabel()
            mg.ifICmp(GeneratorAdapter.GT, skip)
            mg.push(false)
            mg.visitJumpInsn(GOTO, end)
            mg.visitLabel(skip)
            mg.push(true)
            mg.visitLabel(end)
          case OLeq =>
            val skip = mg.newLabel()
            val end = mg.newLabel()
            mg.ifICmp(GeneratorAdapter.LE, skip)
            mg.push(false)
            mg.visitJumpInsn(GOTO, end)
            mg.visitLabel(skip)
            mg.push(true)
            mg.visitLabel(end)
          case OGeq =>
            val skip = mg.newLabel()
            val end = mg.newLabel()
            mg.ifICmp(GeneratorAdapter.GE, skip)
            mg.push(false)
            mg.visitJumpInsn(GOTO, end)
            mg.visitLabel(skip)
            mg.push(true)
            mg.visitLabel(end)

  private def box(t: Ty)(implicit mg: GeneratorAdapter): Unit = t match
    case TInt =>
      mg.invokeStatic(
        Type.getType(classOf[Integer]),
        Method.getMethod("Integer valueOf (int)")
      )
    case _ =>
