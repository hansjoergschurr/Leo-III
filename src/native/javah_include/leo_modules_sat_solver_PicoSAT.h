/* DO NOT EDIT THIS FILE - it is machine generated */
#include <jni.h>
/* Header for class leo_modules_sat_solver_PicoSAT */

#ifndef _Included_leo_modules_sat_solver_PicoSAT
#define _Included_leo_modules_sat_solver_PicoSAT
#ifdef __cplusplus
extern "C" {
#endif
/*
 * Class:     leo_modules_sat_solver_PicoSAT
 * Method:    picosat_init
 * Signature: ()J
 */
JNIEXPORT jlong JNICALL Java_leo_modules_sat_1solver_PicoSAT_picosat_1init
  (JNIEnv *, jobject);

/*
 * Class:     leo_modules_sat_solver_PicoSAT
 * Method:    picosat_enable_trace_generation
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL Java_leo_modules_sat_1solver_PicoSAT_picosat_1enable_1trace_1generation
  (JNIEnv *, jobject, jlong);

/*
 * Class:     leo_modules_sat_solver_PicoSAT
 * Method:    picosat_reset
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_leo_modules_sat_1solver_PicoSAT_picosat_1reset
  (JNIEnv *, jobject, jlong);

/*
 * Class:     leo_modules_sat_solver_PicoSAT
 * Method:    picosat_res
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL Java_leo_modules_sat_1solver_PicoSAT_picosat_1res
  (JNIEnv *, jobject, jlong);

/*
 * Class:     leo_modules_sat_solver_PicoSAT
 * Method:    picosat_inc_max_var
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL Java_leo_modules_sat_1solver_PicoSAT_picosat_1inc_1max_1var
  (JNIEnv *, jobject, jlong);

/*
 * Class:     leo_modules_sat_solver_PicoSAT
 * Method:    picosat_add
 * Signature: (JI)I
 */
JNIEXPORT jint JNICALL Java_leo_modules_sat_1solver_PicoSAT_picosat_1add
  (JNIEnv *, jobject, jlong, jint);

/*
 * Class:     leo_modules_sat_solver_PicoSAT
 * Method:    picosat_sat
 * Signature: (JI)I
 */
JNIEXPORT jint JNICALL Java_leo_modules_sat_1solver_PicoSAT_picosat_1sat
  (JNIEnv *, jobject, jlong, jint);

/*
 * Class:     leo_modules_sat_solver_PicoSAT
 * Method:    picosat_set_global_default_phase
 * Signature: (JI)V
 */
JNIEXPORT void JNICALL Java_leo_modules_sat_1solver_PicoSAT_picosat_1set_1global_1default_1phase
  (JNIEnv *, jobject, jlong, jint);

/*
 * Class:     leo_modules_sat_solver_PicoSAT
 * Method:    picosat_set_default_phase_lit
 * Signature: (JII)V
 */
JNIEXPORT void JNICALL Java_leo_modules_sat_1solver_PicoSAT_picosat_1set_1default_1phase_1lit
  (JNIEnv *, jobject, jlong, jint, jint);

/*
 * Class:     leo_modules_sat_solver_PicoSAT
 * Method:    picosat_reset_phases
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_leo_modules_sat_1solver_PicoSAT_picosat_1reset_1phases
  (JNIEnv *, jobject, jlong);

/*
 * Class:     leo_modules_sat_solver_PicoSAT
 * Method:    picosat_reset_scores
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_leo_modules_sat_1solver_PicoSAT_picosat_1reset_1scores
  (JNIEnv *, jobject, jlong);

/*
 * Class:     leo_modules_sat_solver_PicoSAT
 * Method:    picosat_remove_learned
 * Signature: (JI)V
 */
JNIEXPORT void JNICALL Java_leo_modules_sat_1solver_PicoSAT_picosat_1remove_1learned
  (JNIEnv *, jobject, jlong, jint);

/*
 * Class:     leo_modules_sat_solver_PicoSAT
 * Method:    picosat_set_more_important_lit
 * Signature: (JI)V
 */
JNIEXPORT void JNICALL Java_leo_modules_sat_1solver_PicoSAT_picosat_1set_1more_1important_1lit
  (JNIEnv *, jobject, jlong, jint);

/*
 * Class:     leo_modules_sat_solver_PicoSAT
 * Method:    picosat_set_less_important_lit
 * Signature: (JI)V
 */
JNIEXPORT void JNICALL Java_leo_modules_sat_1solver_PicoSAT_picosat_1set_1less_1important_1lit
  (JNIEnv *, jobject, jlong, jint);

/*
 * Class:     leo_modules_sat_solver_PicoSAT
 * Method:    picosat_adjust
 * Signature: (JI)V
 */
JNIEXPORT void JNICALL Java_leo_modules_sat_1solver_PicoSAT_picosat_1adjust
  (JNIEnv *, jobject, jlong, jint);

/*
 * Class:     leo_modules_sat_solver_PicoSAT
 * Method:    picosat_variables
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL Java_leo_modules_sat_1solver_PicoSAT_picosat_1variables
  (JNIEnv *, jobject, jlong);

/*
 * Class:     leo_modules_sat_solver_PicoSAT
 * Method:    picosat_added_original_clauses
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL Java_leo_modules_sat_1solver_PicoSAT_picosat_1added_1original_1clauses
  (JNIEnv *, jobject, jlong);

/*
 * Class:     leo_modules_sat_solver_PicoSAT
 * Method:    picosat_seconds
 * Signature: (J)D
 */
JNIEXPORT jdouble JNICALL Java_leo_modules_sat_1solver_PicoSAT_picosat_1seconds
  (JNIEnv *, jobject, jlong);

/*
 * Class:     leo_modules_sat_solver_PicoSAT
 * Method:    picosat_assume
 * Signature: (JI)V
 */
JNIEXPORT void JNICALL Java_leo_modules_sat_1solver_PicoSAT_picosat_1assume
  (JNIEnv *, jobject, jlong, jint);

/*
 * Class:     leo_modules_sat_solver_PicoSAT
 * Method:    picosat_deref
 * Signature: (JI)I
 */
JNIEXPORT jint JNICALL Java_leo_modules_sat_1solver_PicoSAT_picosat_1deref
  (JNIEnv *, jobject, jlong, jint);

/*
 * Class:     leo_modules_sat_solver_PicoSAT
 * Method:    picosat_deref_toplevel
 * Signature: (JI)I
 */
JNIEXPORT jint JNICALL Java_leo_modules_sat_1solver_PicoSAT_picosat_1deref_1toplevel
  (JNIEnv *, jobject, jlong, jint);

/*
 * Class:     leo_modules_sat_solver_PicoSAT
 * Method:    picosat_inconsistent
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL Java_leo_modules_sat_1solver_PicoSAT_picosat_1inconsistent
  (JNIEnv *, jobject, jlong);

/*
 * Class:     leo_modules_sat_solver_PicoSAT
 * Method:    picosat_failed_assumption
 * Signature: (JI)I
 */
JNIEXPORT jint JNICALL Java_leo_modules_sat_1solver_PicoSAT_picosat_1failed_1assumption
  (JNIEnv *, jobject, jlong, jint);

/*
 * Class:     leo_modules_sat_solver_PicoSAT
 * Method:    picosat_failed_assumptions
 * Signature: (J)[I
 */
JNIEXPORT jintArray JNICALL Java_leo_modules_sat_1solver_PicoSAT_picosat_1failed_1assumptions
  (JNIEnv *, jobject, jlong);

/*
 * Class:     leo_modules_sat_solver_PicoSAT
 * Method:    picosat_changed
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL Java_leo_modules_sat_1solver_PicoSAT_picosat_1changed
  (JNIEnv *, jobject, jlong);

/*
 * Class:     leo_modules_sat_solver_PicoSAT
 * Method:    picosat_coreclause
 * Signature: (JI)I
 */
JNIEXPORT jint JNICALL Java_leo_modules_sat_1solver_PicoSAT_picosat_1coreclause
  (JNIEnv *, jobject, jlong, jint);

/*
 * Class:     leo_modules_sat_solver_PicoSAT
 * Method:    picosat_corelit
 * Signature: (JI)I
 */
JNIEXPORT jint JNICALL Java_leo_modules_sat_1solver_PicoSAT_picosat_1corelit
  (JNIEnv *, jobject, jlong, jint);

/*
 * Class:     leo_modules_sat_solver_PicoSAT
 * Method:    picosat_usedlit
 * Signature: (JI)I
 */
JNIEXPORT jint JNICALL Java_leo_modules_sat_1solver_PicoSAT_picosat_1usedlit
  (JNIEnv *, jobject, jlong, jint);

#ifdef __cplusplus
}
#endif
#endif
