import scala.language.implicitConversions
import scala.reflect.runtime.universe._

class ReflectiveClosure[A, B](val tree: Tree, fn: Function1[A, B]) extends Function1[A, B] {
  def apply(x: A) = fn(x)
}

object ReflectiveClosure {
  implicit def reflectClosure[A, B](f: Function1[A,B]): ReflectiveClosure[A, B] = new ReflectiveClosure(EmptyTree, f)
}

object Inference {
  implicit class PimpedList[T](val list: List[T]) {
    def query(predicate: ReflectiveClosure[T, Boolean]): List[T] = {
      println(predicate.tree)
      list filter predicate
    }
  }

  List(1, 2, 3).query(x => x % 2 == 0)
}
