package org.scalalang.spores
package typechecker

trait ContextErrors {
  self: Analyzer =>

  import global._
  import ErrorUtils._
  import scala.reflect.internal.util.StringOps._

  trait SporeTyperContextErrors extends TyperContextErrors {
    self: Typer =>

    import infer.setError

    object SporeTyperErrorGen {
      implicit val contextTyperErrorGen: Context = infer.getContext

      def WrongNumberOfParametersError(tree: Tree, expectedArity: Int) = {
        issueNormalTypeError(tree, s"wrong number of parameters; expected ${countAsString(expectedArity)}")
        setError(tree)
      }
    }
  }
}
