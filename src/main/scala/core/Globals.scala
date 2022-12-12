package core

import common.Common.*
import Syntax.{Tm, Ty}
import Value.{Val, VTy}

import scala.collection.mutable

object Globals:
  private val map: mutable.Map[Name, GlobalEntry] = mutable.Map.empty

  def reset(): Unit = map.clear()

  final case class GlobalEntry(
      name: Name,
      tm: Tm,
      ty: Ty,
      value: Val,
      vty: VTy,
      univ: VTy
  )

  def setGlobal(entry: GlobalEntry): Unit = map.put(entry.name, entry)
  def getGlobal(name: Name): Option[GlobalEntry] = map.get(name)
