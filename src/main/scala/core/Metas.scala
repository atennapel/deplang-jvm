package core

import common.Common.*
import core.Syntax.*
import core.Value.*

import scala.collection.mutable.ArrayBuffer

object Metas:
  private var metas: ArrayBuffer[MetaEntry] = ArrayBuffer.empty

  enum MetaEntry:
    case Unsolved
    case Solved(value: Val, tm: Tm)
  export MetaEntry.*

  def freshMeta(): MetaId =
    val id = metaId(metas.size)
    metas.addOne(Unsolved)
    id

  def getMeta(id: MetaId): MetaEntry = metas(id.expose)
  def getMetaUnsolved(id: MetaId): Unit = getMeta(id) match
    case u @ Unsolved => ()
    case Solved(_, _) => impossible()
  def getMetaSolved(id: MetaId): Solved = getMeta(id) match
    case Unsolved         => impossible()
    case s @ Solved(_, _) => s
  def modifyMeta(id: MetaId)(fn: MetaEntry => MetaEntry): Unit =
    metas(id.expose) = fn(metas(id.expose))

  def solveMeta(id: MetaId, v: Val, tm: Tm): Unit =
    getMetaUnsolved(id)
    metas(id.expose) = Solved(v, tm)

  def unsolvedMetas(): List[MetaId] = metas.zipWithIndex.collect {
    case (Unsolved, ix) => metaId(ix)
  }.toList

  def resetMetas(): Unit = metas.clear()
