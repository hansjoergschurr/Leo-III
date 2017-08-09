package leo.modules.special_processing

/**
  * Created by Hans-Jörg Schurr on 11/25/16.
  */

import leo.Configuration
import leo.datastructures.{AnnotatedClause, Signature}
import leo.modules.output.logger.Out

object PreprocessingControl {
  final def satBasedUnitClauses(clSet: Set[AnnotatedClause])(implicit sig: Signature): Set[AnnotatedClause] = {
    SatBasedUnitClauses.findUnitClauses(clSet)
  }

  final def universalReduction(clSet: Set[AnnotatedClause])(implicit sig: Signature): Set[AnnotatedClause] = {
    UniversalReduction.removeUniversalVariables(clSet)
  }

  final def blockedClauseElimination(clSet: Set[AnnotatedClause])(implicit  sig: Signature): Set[AnnotatedClause] = {
    if(BlockedClauseElimination.isEqualityFree(clSet))
      BlockedClauseElimination.removeBlockedClauses(clSet)
    else {
      Out.debug("Problem not equality free. Skipping Blocked Clause Elimination")
      clSet
    }
  }

  final def firstOrderReEncoding(clSet: Set[AnnotatedClause])(implicit sig: Signature): Set[AnnotatedClause] = {
    val wrapEqs = Configuration.isSet("fre_wrapEqs")
    FirstOrderReEncoding.reencodeBooleans(clSet, wrapEqs)
  }
}