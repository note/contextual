/* Contextual, version 1.1.0. Copyright 2018 Jon Pretty, Propensive Ltd.
 *
 * The primary distribution site is: http://co.ntextu.al/
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file
 * except in compliance with the License. You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software distributed under the
 * License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
 * either express or implied. See the License for the specific language governing permissions
 * and limitations under the License.
 */
package contextual

import scala.reflect._, macros.whitebox
import magnolia._

import language.experimental.macros

/** Macro bundle class containing the main macro providing Contextual's functionality. */
object Macros {

  def contextual[C <: Context, I <: Interpolator { type ContextType = C }: c.WeakTypeTag]
      (c: whitebox.Context)(expressions: c.Tree*): c.Tree = {
    import c.universe.{Literal => AstLiteral, _}

    /* Get the string literals from the constructed `StringContext`. */
    val astLiterals = c.prefix.tree match {
      case Select(Apply(_, List(Apply(_, lits))), _)           => lits
      case Select(Apply(Apply(_, List(Apply(_, lits))), _), _) => lits
    }

    val stringLiterals: Seq[String] = astLiterals.map {
      case AstLiteral(Constant(str: String)) => str
    }

    /* Get the "context" types derived from each parameter. */
    val appliedParameters: Seq[Tree] = c.macroApplication match {
      case Apply(_, params) => params
    }

    /* Work out Java name of the class we want to instantiate. This is necessary because classes
     * defined within objects have the names of their parent objects encoded in their class
     * names, yet are presented in symbols in the standard "dotted" style, e.g.
     * `package.Object.Class` is encoded as `package.Object$Class`. */
    def javaClassName(sym: Symbol): String =
      if(sym.owner.isPackage) sym.fullName
      else if(sym.owner.isModuleClass) s"${javaClassName(sym.owner)}$$${sym.name}"
      else s"${javaClassName(sym.owner)}.${sym.name}"

    def getModule[M](tpe: Type): M = {
      val typeName = javaClassName(tpe.typeSymbol)

      try {
        val cls = Class.forName(s"$typeName$$")
        cls.getField("MODULE$").get(cls).asInstanceOf[M]
      } catch {
        case e: ClassNotFoundException =>
          c.abort(c.enclosingPosition, s"""Class "${typeName}" could not be found. This usually means you are trying to use an interpolator in the same compilation unit as the one in which you defined it. Please try compiling interpolators first, separately from the code using them.""")
      }
    }

    /* Get an instance of the Interpolator class. */
    val interpolator = try getModule[I](weakTypeOf[I]) catch {
      case e: Exception => c.abort(c.enclosingPosition, e.toString)
    }

    val parameterTypes: Seq[interpolator.Hole] = appliedParameters.zipWithIndex.map {
      case (Apply(Apply(TypeApply(_, List(contextType, _, _, _)), _), _), idx) =>
        val types: Set[Type] = contextType.tpe match {
          case SingleType(_, singletonType) => Set(singletonType.typeSignature)
          case RefinedType(intersectionTypes, _) => intersectionTypes.to[Set]
          case typ: Type => Set(typ)
        }

        val contextObjects = types.map { t =>
          (getModule[C](t.typeArgs(0)), getModule[C](t.typeArgs(1)))
        }.toMap

        interpolator.Hole(idx, contextObjects)
    }

    val interpolation: interpolator.StaticInterpolation { val macroContext: c.type } =
      new interpolator.StaticInterpolation {
        val macroContext: c.type = c
        val literals: Seq[String] = stringLiterals
        val holes: Seq[interpolator.Hole] = parameterTypes

        def holeTrees: Seq[c.Tree] = expressions
        def literalTrees: Seq[c.Tree] = astLiterals
        def interpolatorTerm: c.Symbol = weakTypeOf[I].termSymbol
      }

    val contexts: Seq[interpolator.ContextType] = interpolator.contextualize(interpolation)

    if(contexts.size != interpolation.holes.size)
      c.abort(
        c.enclosingPosition,
        s"`contextualize` must return exactly one ContextType for each hole"
      )

    interpolator.evaluator(contexts, interpolation)
  }
}


object Construct {

  type Typeclass[T] = Construct[T]

  def dispatch[T](sealedTrait: SealedTrait[Construct, T]): Construct[T] = new Construct[T] {
    def make(c: whitebox.Context)(value: T): c.Tree =
      sealedTrait.dispatch(value) { subtype: Subtype[Construct, T] =>
        subtype.typeclass.make(c)(subtype.cast(value))
      }
  }

  def combine[T](caseClass: CaseClass[Construct, T]): Construct[T] = new Construct[T] {
    def make(c: whitebox.Context)(value: T): c.Tree = {
      import c.universe._
      val term = TermName(s"_root_.${caseClass.typeName.full}")
      val params = caseClass.parameters.map { param: Param[Construct, T] =>
        param.typeclass.make(c)(param.dereference(value))
      }
      q"""$term(..$params)"""
    }
  }

  implicit def gen[T]: Construct[T] = macro Magnolia.gen[T]

  implicit val string: Construct[String] = new Construct[String] {
    def make(c: whitebox.Context)(value: String): c.Tree =
      c.universe.Literal(c.universe.Constant(value))
  }
  
  implicit val int: Construct[Int] = new Construct[Int] {
    def make(c: whitebox.Context)(value: Int): c.Tree =
      c.universe.Literal(c.universe.Constant(value))
  }
  
  implicit val byte: Construct[Byte] = new Construct[Byte] {
    def make(c: whitebox.Context)(value: Byte): c.Tree =
      c.universe.Literal(c.universe.Constant(value))
  }
  
  implicit val short: Construct[Short] = new Construct[Short] {
    def make(c: whitebox.Context)(value: Short): c.Tree =
      c.universe.Literal(c.universe.Constant(value))
  }
  
  implicit val long: Construct[Long] = new Construct[Long] {
    def make(c: whitebox.Context)(value: Long): c.Tree =
      c.universe.Literal(c.universe.Constant(value))
  }
  
  implicit val double: Construct[Double] = new Construct[Double] {
    def make(c: whitebox.Context)(value: Double): c.Tree =
      c.universe.Literal(c.universe.Constant(value))
  }
  
  implicit val float: Construct[Float] = new Construct[Float] {
    def make(c: whitebox.Context)(value: Float): c.Tree =
      c.universe.Literal(c.universe.Constant(value))
  }
  
  implicit val boolean: Construct[Boolean] = new Construct[Boolean] {
    def make(c: whitebox.Context)(value: Boolean): c.Tree =
      c.universe.Literal(c.universe.Constant(value))
  }
  
  implicit val symbol: Construct[Symbol] = new Construct[Symbol] {
    def make(c: whitebox.Context)(value: Symbol): c.Tree = {
      import c.universe._
      q"""_root_.scala.Symbol(${value.name})"""
    }
  }
}

trait Construct[T] { def make(c: whitebox.Context)(value: T): c.Tree }
