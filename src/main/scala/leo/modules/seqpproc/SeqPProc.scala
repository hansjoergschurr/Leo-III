package leo.modules.seqpproc

import leo.Configuration
import leo.Out
import leo.datastructures.{ClauseAnnotation, AnnotatedClause, tptp, Term, Signature, Clause, Literal, addProp}
import leo.modules.output._
import leo.modules.control.Control
import leo.modules.{Parsing, SZSException, SZSOutput, Utility}
import leo.modules.boolean_handling.SatBasedUnitClauses
import leo.modules.boolean_handling.PreprocessingControl

import scala.annotation.tailrec

/**
  * Sequential proof procedure. Its state is represented by [[leo.modules.seqpproc.State]].
  *
  * @since 28.10.15
  * @author Alexander Steen <a.steen@fu-berlin.de>
  */
object SeqPProc {
  type LocalState = State[AnnotatedClause]
  ////////////////////////////////////
  //// Loading and converting the problem
  ////////////////////////////////////
  /** Converts the input into clauses and filters the axioms if applicable. */
  final private def effectiveInput(input: Seq[tptp.Commons.AnnotatedFormula], state: LocalState): Seq[AnnotatedClause] = {
    Out.info(s"Parsing finished. Scanning for conjecture ...")
    val (effectiveInput,conj) = effectiveInput0(input, state)
    if (state.negConjecture != null) {
      Out.info(s"Found a conjecture and ${effectiveInput.size} axioms. Running axiom selection ...")
      // Do relevance filtering: Filter hopefully unnecessary axioms
      val relevantAxioms = Control.getRelevantAxioms(effectiveInput, conj)(state.signature)
      Out.info(s"Axiom selection finished. Selected ${relevantAxioms.size} axioms " +
        s"(removed ${effectiveInput.size - relevantAxioms.size} axioms).")
      relevantAxioms.map(ax => processInput(ax, state))
    } else {
      Out.info(s"${effectiveInput.size} axioms and no conjecture found.")
      effectiveInput.map(ax => processInput(ax, state))
    }
  }
  /** Insert types, definitions and the conjecture to the signature resp. state. The rest
    * (axioms etc.) is left unchanged for relevance filtering. Throws an error if multiple
    * conjectures are present or unknown role occurs. */
  final private def effectiveInput0(input: Seq[tptp.Commons.AnnotatedFormula], state: LocalState): (Seq[tptp.Commons.AnnotatedFormula], tptp.Commons.AnnotatedFormula) = {
    import leo.modules.Utility.termToClause
    import leo.datastructures.{Role_Definition, Role_Type, Role_Conjecture, Role_NegConjecture, Role_Unknown}
    import leo.datastructures.ClauseAnnotation._
    var result: Seq[tptp.Commons.AnnotatedFormula] = Seq()
    var conj: tptp.Commons.AnnotatedFormula = null
    val inputIt = input.iterator
    while (inputIt.hasNext) {
      val formula = inputIt.next()
      formula.role match {
        case Role_Definition.pretty | Role_Type.pretty => Parsing.processFormula(formula)(state.signature)
        case Role_Conjecture.pretty =>
          if (state.negConjecture == null) {
            // Convert and negate and add conjecture
            import leo.modules.calculus.CalculusRule
            val translated = Parsing.processFormula(formula)(state.signature)
            val conjectureClause = AnnotatedClause(termToClause(translated._2), Role_Conjecture, FromFile(Configuration.PROBLEMFILE, translated._1), ClauseAnnotation.PropNoProp)
            state.setConjecture(conjectureClause)
            val negConjectureClause = AnnotatedClause(termToClause(translated._2, false), Role_NegConjecture, InferredFrom(new CalculusRule {
              override final val name: String = "neg_conjecture"
              override final val inferenceStatus = Some(SZS_CounterTheorem)
            }, Set(conjectureClause)), ClauseAnnotation.PropSOS)
            state.setNegConjecture(negConjectureClause)
            conj = formula
          } else throw new SZSException(SZS_InputError, "At most one conjecture per input problem is permitted.")
        case Role_NegConjecture.pretty =>
          if (state.negConjecture == null) {
            val translated = Parsing.processFormula(formula)(state.signature)
            val negConjectureClause = AnnotatedClause(termToClause(translated._2), Role_NegConjecture, FromFile(Configuration.PROBLEMFILE, translated._1), ClauseAnnotation.PropSOS)
            state.setNegConjecture(negConjectureClause)
            conj = formula
          } else throw new SZSException(SZS_InputError, "At most one (negated) conjecture per input problem is permitted.")
        case Role_Unknown.pretty =>
          throw new SZSException(SZS_InputError, s"Formula ${formula.name} has role 'unknown' which is regarded an error.")
        case _ =>
          Control.relevanceFilterAdd(formula)(state.signature)
          result = formula +: result
      }
    }
    (result,conj)
  }
  final private def processInput(input: tptp.Commons.AnnotatedFormula, state: LocalState): AnnotatedClause = {
    import leo.modules.Utility.termToClause
    import leo.datastructures.ClauseAnnotation.FromFile
    val formula = Parsing.processFormula(input)(state.signature)
    AnnotatedClause(termToClause(formula._2), formula._3, FromFile(Configuration.PROBLEMFILE, formula._1), ClauseAnnotation.PropNoProp)
  }
  final private def typeCheck(input: Seq[AnnotatedClause], state: LocalState): Unit = {
    if (state.negConjecture != null) typeCheck0(state.negConjecture +: input)
    else typeCheck0(input)
  }
  @tailrec
  final private def typeCheck0(input: Seq[AnnotatedClause]): Unit = {
    if (input.nonEmpty) {
      val hd = input.head
      if (!Term.wellTyped(hd.cl.lits.head.left)) {
        leo.Out.severe(s"Input problem did not pass type check: ${hd.id} is ill-typed.")
        throw new SZSException(SZS_TypeError, s"Type error in formula ${hd.id}")
      } else {
        typeCheck0(input.tail)
      }
    }
  }

  ////////////////////////////////////
  //// Preprocessing
  ////////////////////////////////////
  protected[modules] final def preprocess(state: LocalState, cur: AnnotatedClause): Set[AnnotatedClause] = {
    implicit val sig: Signature = state.signature
    var result: Set[AnnotatedClause] = Set()

    // Fresh clause, that means its unit and nonequational
    assert(Clause.unit(cur.cl), "clause not unit")
    val lit = cur.cl.lits.head
    assert(!lit.equational, "initial literal equational")

    // Def expansion and simplification
    val expanded = Control.expandDefinitions(cur)
    val polarityswitchedAndExpanded = Control.switchPolarity(expanded)
    // We may instantiate here special symbols for universal variables
    // Its BEFORE miniscope because their are less quantifiers and maybe
    // some universal quantification may vanish after extensional instantiation
    // Run simp here again to eliminate connectives with true/false as operand due
    // to ext. instantiation.
    result = Control.specialInstances(polarityswitchedAndExpanded)

    result = result.flatMap { cl =>
      Control.cnf(Control.miniscope(cl))
    }

    // TODO: Interplay between choice and defined equalities?
    /*result = result.map {cl =>
      val choiceCandidate = Control.detectChoiceClause(cl)
      if (choiceCandidate.isDefined) {
        val choiceFun = choiceCandidate.get
        state.addChoiceFunction(choiceFun)
        leo.Out.debug(s"Choice: function detected ${choiceFun.pretty(sig)}")
        leo.Out.debug(s"Choice: clause removed ${cl.id}")
        import leo.modules.HOLSignature.LitTrue
        // replace formula by a trivial one: [[true]^t]
        AnnotatedClause(Clause(Literal.mkLit(LitTrue, true)), NoAnnotation)
      } else cl
    }*/
    // Add detected equalities as primitive ones
    result = result union Control.convertDefinedEqualities(result)

    // To equation if possible and then apply func ext
    // AC Simp if enabled, then Simp.
    result = result.map { cl =>
      var result = cl
      result = Control.liftEq(result)
      result = Control.funcext(result) // Maybe comment out? why?
      val possiblyAC = Control.detectAC(result)
      if (possiblyAC.isDefined) {
        val symbol = possiblyAC.get._1
        val spec = possiblyAC.get._2
        val sig = state.signature
        val oldProp = sig(symbol).flag
        if (spec) {
          Out.trace(s"[AC] A/C specification detected: ${result.id} is an instance of commutativity")
          sig(symbol).updateProp(addProp(Signature.PropCommutative, oldProp))
        } else {
          Out.trace(s"[AC] A/C specification detected: ${result.id} is an instance of associativity")
          sig(symbol).updateProp(addProp(Signature.PropAssociative, oldProp))
        }
      }
      result = Control.acSimp(result)
      Control.simp(result)
    }

    // Pre-unify new clauses or treat them extensionally and remove trivial ones
    result = Control.extPreprocessUnify(result)
    result = result.filterNot(cw => Clause.trivial(cw.cl))
    result
  }

  ////////////////////////////////////
  //// Main-loop operations
  ////////////////////////////////////

  /* Main function containing proof loop */
  final def apply(startTime: Long): Unit = {
    /////////////////////////////////////////
    // Main loop preparations:
    // Read Problem, preprocessing, state set-up, etc.
    /////////////////////////////////////////
    implicit val sig: Signature = Signature.freshWithHOL()
    val state: State[AnnotatedClause] = State.fresh(sig)
    // Read problem from file
    val input2 = Parsing.readProblem(Configuration.PROBLEMFILE)
    val startTimeWOParsing = System.currentTimeMillis()
    // Split input in conjecture/definitions/axioms etc.
    val remainingInput: Seq[AnnotatedClause] = effectiveInput(input2, state)
    // Typechecking: Throws and exception if not well-typed
    typeCheck(remainingInput, state)
    // Remaining stuff ...
    Out.info(s"Type checking passed. Searching for refutation ...")
      // Initialize indexes
    if (state.negConjecture != null) Control.initIndexes(state.negConjecture +: remainingInput)
    else Control.initIndexes(remainingInput)

    Out.trace(s"Symbols in conjecture: " +
      s"${state.symbolsInConjecture.map(state.signature(_).name).mkString(",")}")
    // Preprocessing
    val conjecture_preprocessed = if (state.negConjecture != null) {
      Out.debug("## Preprocess Neg.Conjecture BEGIN")
      Out.trace(s"Neg. conjecture: ${state.negConjecture.pretty(sig)}")
      val result = preprocess(state, state.negConjecture).filterNot(cw => Clause.trivial(cw.cl))
      Out.debug(s"# Result:\n\t${
        result.map {
          _.pretty(sig)
        }.mkString("\n\t")
      }")
      Out.trace("## Preprocess Neg.Conjecture END")
      result
    } else Set[AnnotatedClause]()

    Out.debug("## Preprocess BEGIN")
    val preprocessIt = remainingInput.iterator
    while (preprocessIt.hasNext) {
      val cur = preprocessIt.next()
      Out.trace(s"# Process: ${cur.pretty(sig)}")
      val processed = preprocess(state, cur)
      Out.debug(s"# Result:\n\t${
        processed.map {
          _.pretty(sig)
        }.mkString("\n\t")
      }")
      val preprocessed = processed.filterNot(cw => Clause.trivial(cw.cl))
      state.addUnprocessed(preprocessed)
      if (preprocessIt.hasNext) Out.trace("--------------------")
    }

    val satUnitClauses = PreprocessingControl.satBasedUnitClauses(state.unprocessed union conjecture_preprocessed)
    satUnitClauses.foreach(state.addUnprocessed)

    Out.trace("## Preprocess END\n\n")

      // Debug output
      if (Out.logLevelAtLeast(java.util.logging.Level.FINEST)) {
        Out.finest(s"Clauses and maximal literals of them:")
        for (c <- state.unprocessed union conjecture_preprocessed) {
          Out.finest(s"Clause ${c.pretty(sig)}")
          Out.finest(s"Maximal literal(s):")
          Out.finest(s"\t${Literal.maxOf(c.cl.lits).map(_.pretty(sig)).mkString("\n\t")}")
        }
      }
      Out.finest(s"################")

      val preprocessTime = System.currentTimeMillis() - startTimeWOParsing
      var loop = true

      /////////////////////////////////////////
      // Init loop for conjecture-derived clauses
      /////////////////////////////////////////
      val conjectureProcessedIt = conjecture_preprocessed.iterator
      Out.debug("## Pre-reasoning loop BEGIN")
      while (conjectureProcessedIt.hasNext && loop && !prematureCancel(state.noProcessedCl)) {
        if (System.currentTimeMillis() - startTime > 1000 * Configuration.TIMEOUT) {
          loop = false
          state.setSZSStatus(SZS_Timeout)
        } else {
          var cur = conjectureProcessedIt.next()
          Out.debug(s"Taken: ${cur.pretty(sig)}")
          cur = Control.rewriteSimp(cur, state.rewriteRules)
          /* Functional Extensionality */
          cur = Control.funcext(cur)
          /* To equality if possible */
          cur = Control.liftEq(cur)
          if (Clause.effectivelyEmpty(cur.cl)) {
            loop = false
            if (state.conjecture == null) {
              state.setSZSStatus(SZS_Unsatisfiable)
            } else {
              state.setSZSStatus(SZS_Theorem)
            }
            state.setDerivationClause(cur)
          } else {
            val choiceCandidate = Control.detectChoiceClause(cur)
            if (choiceCandidate.isDefined) {
              val choiceFun = choiceCandidate.get
              state.addChoiceFunction(choiceFun)
              leo.Out.debug(s"Choice function detected: ${choiceFun.pretty(sig)}")
            } else {
              // Redundancy check: Check if cur is redundant wrt to the set of processed clauses
              // e.g. by forward subsumption
              if (!Control.redundant(cur, state.processed)) {
                if(mainLoopInferences(cur, state)) loop = false
              } else {
                Out.debug(s"Clause ${cur.id} redundant, skipping.")
                state.incForwardSubsumedCl()
              }
            }
          }
        }
      }
      Out.debug("## Pre-reasoning loop END")

      /////////////////////////////////////////
      // Main proof loop TODO: Merge with pre-reasoning loop
      /////////////////////////////////////////
      Out.debug("## Reasoning loop BEGIN")
      while (loop && !prematureCancel(state.noProcessedCl)) {
        if (System.currentTimeMillis() - startTime > 1000 * Configuration.TIMEOUT) {
          loop = false
          state.setSZSStatus(SZS_Timeout)
        } else if (!state.unprocessedLeft) {
          loop = false
        } else {
          // No cancel, do reasoning step
          var cur = state.nextUnprocessed
          // cur is the current AnnotatedClause
          Out.debug(s"Taken: ${cur.pretty(sig)}")
          Out.trace(s"Maximal: ${Literal.maxOf(cur.cl.lits).map(_.pretty(sig)).mkString("\n\t")}")

          cur = Control.rewriteSimp(cur, state.rewriteRules)
          /* Functional Extensionality */
          cur = Control.funcext(cur)
          /* To equality if possible */
          cur = Control.liftEq(cur)
          // Check if `cur` is an empty clause
          if (Clause.effectivelyEmpty(cur.cl)) {
            loop = false
            endplay(cur, state)
          } else {
            // Not an empty clause, detect choice definition or do reasoning step.
            val choiceCandidate = Control.detectChoiceClause(cur)
            if (choiceCandidate.isDefined) {
              val choiceFun = choiceCandidate.get
              state.addChoiceFunction(choiceFun)
              leo.Out.debug(s"Choice function detected: ${choiceFun.pretty(sig)}")
            } else {
              // Redundancy check: Check if cur is redundant wrt to the set of processed clauses
              // e.g. by forward subsumption
              if (!Control.redundant(cur, state.processed)) {
                if(mainLoopInferences(cur, state)) loop = false
              } else {
                Out.debug(s"Clause ${cur.id} redundant, skipping.")
                state.incForwardSubsumedCl()
              }
            }
          }
        }
      }

      /////////////////////////////////////////
      // Main loop terminated, print result
      /////////////////////////////////////////

      val time = System.currentTimeMillis() - startTime
      val timeWOParsing = System.currentTimeMillis() - startTimeWOParsing

      Out.output("")
      Out.output(SZSOutput(state.szsStatus, Configuration.PROBLEMFILE, s"$time ms resp. $timeWOParsing ms w/o parsing"))

      /* Output additional information about the reasoning process. */
      Out.comment(s"Time passed: ${time}ms")
      Out.comment(s"Effective reasoning time: ${timeWOParsing}ms")
      Out.comment(s"Thereof preprocessing: ${preprocessTime}ms")
      val proof = if (state.derivationClause.isDefined) Utility.proofOf(state.derivationClause.get) else null
      if (proof != null)
        Out.comment(s"No. of axioms used: ${Utility.axiomsInProof(proof).size}")
      Out.comment(s"No. of processed clauses: ${state.noProcessedCl}")
      Out.comment(s"No. of generated clauses: ${state.noGeneratedCl}")
      Out.comment(s"No. of forward subsumed clauses: ${state.noForwardSubsumedCl}")
      Out.comment(s"No. of backward subsumed clauses: ${state.noBackwardSubsumedCl}")
      Out.comment(s"No. of units in store: ${state.rewriteRules.size}")
      Out.comment(s"No. of choice functions detected: ${state.choiceFunctionCount}")
      Out.comment(s"No. of choice instantiations: ${state.choiceInstantiations}")
      Out.debug(s"literals processed: ${state.processed.flatMap(_.cl.lits).size}")
      Out.debug(s"-thereof maximal ones: ${state.processed.flatMap(c => Literal.maxOf(c.cl.lits)).size}")
      Out.debug(s"avg. literals per clause: ${state.processed.flatMap(_.cl.lits).size / state.processed.size.toDouble}")
      Out.debug(s"avg. max. literals per clause: ${state.processed.flatMap(c => Literal.maxOf(c.cl.lits)).size / state.processed.size.toDouble}")
      Out.debug(s"oriented processed: ${state.processed.flatMap(_.cl.lits).count(_.oriented)}")
      Out.debug(s"oriented unprocessed: ${state.unprocessed.flatMap(_.cl.lits).count(_.oriented)}")
      Out.debug(s"unoriented processed: ${state.processed.flatMap(_.cl.lits).count(!_.oriented)}")
      Out.debug(s"unoriented unprocessed: ${state.unprocessed.flatMap(_.cl.lits).count(!_.oriented)}")
      Out.debug(s"subsumption tests: ${leo.modules.calculus.Subsumption.subsumptiontests}")

      Out.finest("#########################")
      Out.finest("units")
      import leo.modules.calculus.PatternUnification.isPattern
      Out.finest(state.rewriteRules.map(cl => s"(${isPattern(cl.cl.lits.head.left)}/${isPattern(cl.cl.lits.head.right)}): ${cl.pretty(sig)}").mkString("\n\t"))
      Out.finest("#########################")
      Out.finest("#########################")
      Out.finest("#########################")
      Out.finest("Processed unoriented")
      Out.finest("#########################")
      Out.finest(state.processed.flatMap(_.cl.lits).filter(!_.oriented).map(_.pretty(sig)).mkString("\n\t"))
      Out.finest("#########################")
      Out.finest("#########################")
      Out.finest("#########################")
      Out.finest("Unprocessed unoriented")
      Out.finest(state.unprocessed.flatMap(_.cl.lits).filter(!_.oriented).map(_.pretty(sig)).mkString("\n\t"))
      Out.finest("#########################")


      if (Out.logLevelAtLeast(java.util.logging.Level.FINEST)) {
        Out.comment("Signature extension used:")
        Out.comment(s"Name\t|\tId\t|\tType/Kind\t|\tDef.\t|\tProperties")
        Out.comment(Utility.userDefinedSignatureAsString(sig)) // TODO: Adjust for state
      }

      if (Out.logLevelAtLeast(java.util.logging.Level.FINEST)) {
        Out.comment("Clauses at the end of the loop:")
        Out.comment("\t" + state.processed.toSeq.sortBy(_.cl.lits.size).map(_.pretty(sig)).mkString("\n\t"))
      }
      if (Out.logLevelAtLeast(java.util.logging.Level.FINEST)) {
        Out.finest("TFF clauses at the end:")
        Out.finest("\t" + Control.foIndex.iterator.toSeq.map(leo.modules.output.ToTFF.apply).mkString("\n\t"))
      }


      /* Print proof object if possible and requested. */
      if (state.szsStatus == SZS_Theorem && Configuration.PROOF_OBJECT && proof != null) {
        Out.comment(s"SZS output start CNFRefutation for ${Configuration.PROBLEMFILE}")
        Out.output(Utility.userSignatureToTPTP(Utility.symbolsInProof(proof))(sig))
        Out.output(Utility.proofToTPTP(proof))
        Out.comment(s"SZS output end CNFRefutation for ${Configuration.PROBLEMFILE}")
      }
  }

  private final def mainLoopInferences(cl: AnnotatedClause, state: LocalState): Boolean = {
    implicit val sig: Signature = state.signature

    val cur: AnnotatedClause = cl
    var newclauses: Set[AnnotatedClause] = Set()

//    println(s"current clauses symbols: ${Clause.symbols(cl.cl).map(s => state.signature(s).name).mkString(",")}")

    /////////////////////////////////////////
    // Backward simplification BEGIN
    // TODO: à la E: direct descendant criterion, etc.
    /////////////////////////////////////////
    /* Subsumption */
    val backSubsumedClauses = Control.backwardSubsumptionTest(cur, state.processed)
    if (backSubsumedClauses.nonEmpty) {
      Out.trace(s"#### backward subsumed")
      state.incBackwardSubsumedCl(backSubsumedClauses.size)
      Out.trace(s"backward subsumes\n\t${backSubsumedClauses.map(_.pretty(sig)).mkString("\n\t")}")
      state.setProcessed(state.processed -- backSubsumedClauses)
      Control.removeFromIndex(backSubsumedClauses)
    }
    /** Add to processed and to indexes. */
    state.addProcessed(cur)
    Control.insertIndexed(cur)
    /* Add rewrite rules to set */
    if (Clause.rewriteRule(cur.cl)) state.addRewriteRule(cur)
    /////////////////////////////////////////
    // Backward simplification END
    /////////////////////////////////////////
    /////////////////////////////////////////
    // Generating inferences BEGIN
    /////////////////////////////////////////
    /* Boolean Extensionality */
    val boolext_result = Control.boolext(cur)
    newclauses = newclauses union boolext_result

    /* paramodulation where at least one involved clause is `cur` */
    val paramod_result = Control.paramodSet(cur, state.processed)
    newclauses = newclauses union paramod_result

    /* Equality factoring of `cur` */
    val factor_result = Control.factor(cur)
    newclauses = newclauses union factor_result

    /* Prim subst */
    val primSubst_result = Control.primsubst(cur, Configuration.PRIMSUBST_LEVEL)
    newclauses = newclauses union primSubst_result

    /* Replace defined equalities */
    newclauses = newclauses union Control.convertDefinedEqualities(newclauses)
    /* Replace eq symbols on top-level by equational literals. */
    newclauses = newclauses.map(Control.liftEq)

    val choice_result = Control.instantiateChoice(cur, state.choiceFunctions)
    state.incChoiceInstantiations(choice_result.size)
    newclauses = newclauses union choice_result
    /////////////////////////////////////////
    // Generating inferences END
    /////////////////////////////////////////

    /////////////////////////////////////////
    // Simplification of newly generated clauses BEGIN
    /////////////////////////////////////////
    state.incGeneratedCl(newclauses.size)
    /* Simplify new clauses */
//    newclauses = Control.shallowSimpSet(newclauses)
    /* Remove those which are tautologies */
    newclauses = newclauses.filterNot(cw => Clause.trivial(cw.cl))

    /* Pre-unify new clauses */
    newclauses = Control.unifyNewClauses(newclauses)

    /* exhaustively CNF new clauses */
    newclauses = newclauses.flatMap(cw => Control.cnf(cw))
    /* Replace eq symbols on top-level by equational literals. */
    newclauses = newclauses.map(Control.liftEq)
    /////////////////////////////////////////
    // Simplification of newly generated clauses END
    /////////////////////////////////////////

    /////////////////////////////////////////
    // At the end, for each generated clause apply simplification etc.
    // and add to unprocessed, eagly look for the empty clause
    // and return true if found.
    /////////////////////////////////////////
    val newIt = newclauses.iterator
    while (newIt.hasNext) {
      var newCl = newIt.next()
      assert(Clause.wellTyped(newCl.cl), s"clause ${newCl.id} is not well-typed")
      newCl = Control.shallowSimp(newCl)
      if (Clause.effectivelyEmpty(newCl.cl)) {
        endplay(newCl, state)
        return true
      } else {
        if (!Clause.trivial(newCl.cl)) state.addUnprocessed(newCl)
        else Out.trace(s"Trivial, hence dropped: ${newCl.pretty(sig)}")
      }
    }
    false
  }

  @inline final private def endplay(emptyClause: AnnotatedClause, state: LocalState): Unit = {
    if (state.conjecture == null) state.setSZSStatus(SZS_Unsatisfiable)
    else state.setSZSStatus(SZS_Theorem)
    state.setDerivationClause(emptyClause)
  }

  @inline final def prematureCancel(counter: Int): Boolean = {
    try {
      val limit: Int = Configuration.valueOf("ll").get.head.toInt
      counter >= limit
    } catch {
      case e: NumberFormatException => false
      case e: NoSuchElementException => false
    }
  }

  object CallLeo extends leo.modules.calculus.CalculusRule {
    val name = "call_leo2"
    override val inferenceStatus = Some(SZS_Theorem)
  }
}
