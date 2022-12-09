package common

import Common.*
import surface.Syntax as S
import core.Syntax.{Tm, Ty}
import core.Value.{Val, VTy}

import scala.collection.mutable

object Globals:
  private val map: mutable.Map[Name, GlobalEntry] = mutable.Map.empty

  def reset(): Unit = map.clear()

  final case class GlobalEntry(
      name: Name,
      tm: Tm,
      ty: Ty,
      value: Val,
      vty: VTy
  )

  def setGlobal(entry: GlobalEntry): Unit = map.put(entry.name, entry)
  def getGlobal(name: Name): Option[GlobalEntry] = map.get(name)
