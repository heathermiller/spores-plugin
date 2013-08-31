package org.scalalang.spores
package reflect

import scala.language.implicitConversions
import scala.tools.nsc.{Global => NscGlobal}
import scala.tools.nsc.{Settings => NscSettings}
import org.scalalang.spores.{Settings => ParadiseSettings}

trait Enrichments extends Definitions {
  val global: NscGlobal
  implicit def paradiseSettings(settings: NscSettings) = ParadiseSettings
  def installationFailure() = global.abort("failed to install spore plugin")
}
