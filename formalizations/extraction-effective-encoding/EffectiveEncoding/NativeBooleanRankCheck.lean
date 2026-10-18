import EffectiveEncoding.NativeBooleanRankProgram
import EffectiveEncoding.NativeBooleanRankEvaluation

open Lean Elab Command
namespace EffectiveEncodingNativeBooleanRankVerification

def checkKinds (theorems models : List Name) : CommandElabM Unit := do
  let env ← getEnv
  for n in theorems do
    let some ci := env.find? n | throwError "Missing theorem {n}"
    unless ci.isTheorem do throwError "Expected theorem declaration {n}"
  for n in models do
    let some ci := env.find? n | throwError "Missing model {n}"
    match ci with
    | .defnInfo _ => pure ()
    | .inductInfo _ => pure ()
    | _ => throwError "Expected definition or inductive {n}"
  logInfo m!"OWNED_KIND_CHECK_PASS {theorems.length} theorems; {models.length} models"

end EffectiveEncodingNativeBooleanRankVerification

run_cmd (EffectiveEncodingNativeBooleanRankVerification.checkKinds [
  ``EffectiveEncoding.nativeTripleWordProgram_value,
  ``EffectiveEncoding.nativeTripleWordProgram_encodingActions,
  ``EffectiveEncoding.nativeTripleWordProgram_width,
  ``EffectiveEncoding.nativeOrderIsEqual_correct,
  ``EffectiveEncoding.nativeTripleComparisonProgram_equal,
  ``EffectiveEncoding.nativeTripleComparisonProgram_actions,
  ``EffectiveEncoding.nativeTripleScanProgram_index,
  ``EffectiveEncoding.nativeTripleScanProgram_logicalQueryCount,
  ``EffectiveEncoding.nativeTripleScanProgram_testCount,
  ``EffectiveEncoding.nativeTripleScanProgram_comparisonActions,
  ``EffectiveEncoding.nativeTripleWordMap_values,
  ``EffectiveEncoding.nativeBooleanRankProgram_ranked,
  ``EffectiveEncoding.nativeTripleWordMap_encodingActions,
  ``EffectiveEncoding.nativeBooleanRankProgram_booleanActions_bound,
  ``EffectiveEncoding.nativeBooleanRank_algebra,
  ``EffectiveEncoding.nativeBooleanRankProgram_booleanActions_polynomial
] [
  ``EffectiveEncoding.NativeTripleWords,
  ``EffectiveEncoding.nativeTripleWordProgram,
  ``EffectiveEncoding.NativeTripleWords.value,
  ``EffectiveEncoding.NativeTripleWords.encodingActions,
  ``EffectiveEncoding.NativeTripleWords.Width,
  ``EffectiveEncoding.nativeOrderIsEqual,
  ``EffectiveEncoding.NativeTripleComparison,
  ``EffectiveEncoding.nativeTripleComparisonProgram,
  ``EffectiveEncoding.NativeTripleComparison.actions,
  ``EffectiveEncoding.NativeTripleScanResult,
  ``EffectiveEncoding.nativeTripleScanProgram,
  ``EffectiveEncoding.NativeTripleScanResult.comparisonActions,
  ``EffectiveEncoding.NativeBooleanRankResult,
  ``EffectiveEncoding.nativeBooleanRankProgram,
  ``EffectiveEncoding.NativeBooleanRankResult.booleanActions
])

#check EffectiveEncoding.nativeTripleWordProgram_value
#print axioms EffectiveEncoding.nativeTripleWordProgram_value
#check EffectiveEncoding.nativeTripleWordProgram_encodingActions
#print axioms EffectiveEncoding.nativeTripleWordProgram_encodingActions
#check EffectiveEncoding.nativeTripleWordProgram_width
#print axioms EffectiveEncoding.nativeTripleWordProgram_width
#check EffectiveEncoding.nativeOrderIsEqual_correct
#print axioms EffectiveEncoding.nativeOrderIsEqual_correct
#check EffectiveEncoding.nativeTripleComparisonProgram_equal
#print axioms EffectiveEncoding.nativeTripleComparisonProgram_equal
#check EffectiveEncoding.nativeTripleComparisonProgram_actions
#print axioms EffectiveEncoding.nativeTripleComparisonProgram_actions
#check EffectiveEncoding.nativeTripleScanProgram_index
#print axioms EffectiveEncoding.nativeTripleScanProgram_index
#check EffectiveEncoding.nativeTripleScanProgram_logicalQueryCount
#print axioms EffectiveEncoding.nativeTripleScanProgram_logicalQueryCount
#check EffectiveEncoding.nativeTripleScanProgram_testCount
#print axioms EffectiveEncoding.nativeTripleScanProgram_testCount
#check EffectiveEncoding.nativeTripleScanProgram_comparisonActions
#print axioms EffectiveEncoding.nativeTripleScanProgram_comparisonActions
#check EffectiveEncoding.nativeTripleWordMap_values
#print axioms EffectiveEncoding.nativeTripleWordMap_values
#check EffectiveEncoding.nativeBooleanRankProgram_ranked
#print axioms EffectiveEncoding.nativeBooleanRankProgram_ranked
#check EffectiveEncoding.nativeTripleWordMap_encodingActions
#print axioms EffectiveEncoding.nativeTripleWordMap_encodingActions
#check EffectiveEncoding.nativeBooleanRankProgram_booleanActions_bound
#print axioms EffectiveEncoding.nativeBooleanRankProgram_booleanActions_bound
#check EffectiveEncoding.nativeBooleanRank_algebra
#print axioms EffectiveEncoding.nativeBooleanRank_algebra
#check EffectiveEncoding.nativeBooleanRankProgram_booleanActions_polynomial
#print axioms EffectiveEncoding.nativeBooleanRankProgram_booleanActions_polynomial
#check EffectiveEncoding.NativeTripleWords
#print axioms EffectiveEncoding.NativeTripleWords
#check EffectiveEncoding.nativeTripleWordProgram
#print axioms EffectiveEncoding.nativeTripleWordProgram
#check EffectiveEncoding.NativeTripleWords.value
#print axioms EffectiveEncoding.NativeTripleWords.value
#check EffectiveEncoding.NativeTripleWords.encodingActions
#print axioms EffectiveEncoding.NativeTripleWords.encodingActions
#check EffectiveEncoding.NativeTripleWords.Width
#print axioms EffectiveEncoding.NativeTripleWords.Width
#check EffectiveEncoding.nativeOrderIsEqual
#print axioms EffectiveEncoding.nativeOrderIsEqual
#check EffectiveEncoding.NativeTripleComparison
#print axioms EffectiveEncoding.NativeTripleComparison
#check EffectiveEncoding.nativeTripleComparisonProgram
#print axioms EffectiveEncoding.nativeTripleComparisonProgram
#check EffectiveEncoding.NativeTripleComparison.actions
#print axioms EffectiveEncoding.NativeTripleComparison.actions
#check EffectiveEncoding.NativeTripleScanResult
#print axioms EffectiveEncoding.NativeTripleScanResult
#check EffectiveEncoding.nativeTripleScanProgram
#print axioms EffectiveEncoding.nativeTripleScanProgram
#check EffectiveEncoding.NativeTripleScanResult.comparisonActions
#print axioms EffectiveEncoding.NativeTripleScanResult.comparisonActions
#check EffectiveEncoding.NativeBooleanRankResult
#print axioms EffectiveEncoding.NativeBooleanRankResult
#check EffectiveEncoding.nativeBooleanRankProgram
#print axioms EffectiveEncoding.nativeBooleanRankProgram
#check EffectiveEncoding.NativeBooleanRankResult.booleanActions
#print axioms EffectiveEncoding.NativeBooleanRankResult.booleanActions
