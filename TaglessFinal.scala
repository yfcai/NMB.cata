import scala.language.implicitConversions

trait TaglessFinal extends NameBindingLanguage {
  // ADT gives us fold, the "initial view" on a data structure.
  // Here's the "final view".
  // It encodes pattern matching but is unrelated to recursion.

  type Final[T] = Functor[ADT] => T

  abstract class FinalRepr {
    def apply[T](f: Final[T]): T

    def toADT: ADT = apply(_.toADT)
  }

  implicit class ToFinal(t: ADT) {
    def foldFinal[T](f: Final[T]): T =
      t.fold[FinalRepr]({
        case s: Functor[FinalRepr] => new FinalRepr {
          def apply[R](g: Final[R]): R = g(s map (_.toADT))
        }
      })(f)
  }
}

trait TaglessSyntax extends Syntax with TaglessFinal

trait TaglessCalculus extends TaglessSyntax with Values {
  def evalWithEnv(t: ADT)(env: Env[Val]): Val = t.foldFinal[Val] {
    // Note that we have the ConF* variants on left hand side.
    // Tagless-final isn't really necessary now that we generate
    // code anyway.
    case ConF(s)    => lookupVal(s)
    case VarF(x)    => env(x)
    case AppF(f, s) => evalWithEnv(f)(env) apply evalWithEnv(s)(env)
    case AbsF(x, t) => Fun { v =>
      evalWithEnv(t)(({case y if y == x => v}: Env[Val]) orElse env)
    }
  }

  def eval(t: ADT): Val = evalWithEnv(t)(Map.empty)
}

object TestTaglessFinal {
  def main(args: Array[String]) {
    val tagless = new Test with TaglessCalculus { type Domain = Val }
    tagless.testAll
  }
}
