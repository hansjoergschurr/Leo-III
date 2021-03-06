package leo.modules.parsers

import java.nio.file.Paths

import leo.datastructures.ClauseAnnotation.NoAnnotation
import leo.datastructures.context.Context
import leo.datastructures.{AnnotatedClause, Clause, ClauseAnnotation, Literal}
import leo.datastructures.blackboard.impl.FormulaDataStore
import leo.{Checked, Ignored, LeoTestSuite}
import leo.datastructures.blackboard.Blackboard
import leo.datastructures.impl.SignatureImpl
import leo.modules.printSignature

/**
 * This suite tests the parsing and input processing of all the TPTP dialects except for CNF.
 * The suite is based on the SYN000-files that cover basic and advanced syntax features for all
 * dialects.
  *
  * @author Alexander Steen
 * @since 09.02.2015
 */
class InputTestSuite extends LeoTestSuite {
  val source = getClass.getResource("/problems").getPath

  val problem_suffix = ".p"

  val problems = Seq( //"SYN000-1" -> "TPTP CNF basic syntax features",
//                      "SYN000+1" -> "TPTP FOF basic syntax features",
//                      "SYN000_1" -> "TPTP TF0 basic syntax features",
                      "SYN000^1" -> "TPTP THF basic syntax features",
                      "SYN000^2" -> "TPTP THF advanced syntax features"
//                      "SYN000+2" -> "TPTP FOF advanced syntax features",
//                      "SYN000_2" -> "TPTP TF0 advanced syntax features",
//                      "SYN000=2" -> "TPTP TFA with arithmetic advanced syntax features"
  )

  for (p <- problems) {
    test(p._2, Ignored) {
      println(new java.net.URI(getClass.getResource("/problems").getPath).toString)
      println(Paths.get(source).toAbsolutePath.normalize().toString)
      implicit val sig = getFreshSignature
      printHeading(s"Processing test for ${p._2}")
      print(s"## Parsing ${p._1} ...")

      var fs = Input.readProblem("/home/lex/dev/Leo-III/target/leo-iii-0.1-tests.jar!/problems" + "/" + p._1 + ".p").map{case (name, term, role) => AnnotatedClause(Clause(Literal(term, true)), role, NoAnnotation, ClauseAnnotation.PropNoProp)}
      println("Success!")
      println(s"Parsed ${sig.allUserConstants.size} symbols into signature, ${FormulaDataStore.getFormulas.size} formulae added to blackboard.")
      println()
      println("## Problem signature:")
      printLongHLine()
      printSignature(sig)
      println()
      println("## Formulae converted to internal representation:")
      printLongHLine()
//      Utility.formulaContext()
      println()
    }
  }
}
