package org.scalalang.spores
package typechecker

import scala.tools.nsc.typechecker.{Analyzer => NscAnalyzer}
import org.scalalang.spores.reflect.Enrichments

trait Analyzer extends NscAnalyzer
                  with Typers
                  with Enrichments
                  with ContextErrors {

  override def newTyper(context: Context) = new Typer(context) with SporeTyper
}
