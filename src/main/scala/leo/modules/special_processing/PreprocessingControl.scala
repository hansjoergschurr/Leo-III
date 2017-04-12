package leo.modules.special_processing

/**
  * Created by Hans-Jörg Schurr on 11/25/16.
  */

import leo.Configuration
import leo.datastructures.{AnnotatedClause, Signature}

object PreprocessingControl {
  final def satBasedUnitClauses(clSet: Set[AnnotatedClause])(implicit sig: Signature): Set[AnnotatedClause] = {
    SatBasedUnitClauses.findUnitClauses(clSet)
  }

  final def universalReduction(clSet: Set[AnnotatedClause])(implicit sig: Signature): Set[AnnotatedClause] = {
    UniversalReduction.removeUniversalVariables(clSet)
  }

  final def blockedClauseElimination(clSet: Set[AnnotatedClause])(implicit  sig: Signature): Set[AnnotatedClause] = {
    assert(BlockedClauseElimination.isEqualityFree(clSet))
    BlockedClauseElimination.removeBlockedClauses(clSet)
  }

  final def firstOrderReEncoding(clSet: Set[AnnotatedClause])(implicit sig: Signature): Set[AnnotatedClause] = {
    val wrapEqs = Configuration.isSet("fre_dontWrapEqs")
    FirstOrderReEncoding.reencodeBooleans(clSet, !wrapEqs)
  }
}
