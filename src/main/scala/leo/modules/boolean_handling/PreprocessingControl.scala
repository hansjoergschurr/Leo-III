package leo.modules.boolean_handling

/**
  * Created by Hans-Jörg Schurr on 11/25/16.
  */

import leo.datastructures.{AnnotatedClause, Signature}

object PreprocessingControl {
     final def satBasedUnitClauses(clSet: Set[AnnotatedClause])(implicit sig: Signature): Set[AnnotatedClause] = {
          SatBasedUnitClauses.findUnitClauses(clSet)
     }
}
