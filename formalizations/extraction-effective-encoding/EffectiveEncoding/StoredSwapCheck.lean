import EffectiveEncoding.StoredSwapExtraction

open Lean Elab Command
namespace EffectiveEncodingStoredSwapVerification

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

end EffectiveEncodingStoredSwapVerification

run_cmd (EffectiveEncodingStoredSwapVerification.checkKinds [
  ``EffectiveEncoding.applyStoredSwaps_value,
  ``EffectiveEncoding.applyStoredSwaps_count,
  ``EffectiveEncoding.storedAlignmentRun_word,
  ``EffectiveEncoding.storedAlignmentRun_count,
  ``EffectiveEncoding.storedAlignmentRun_empty_word,
  ``EffectiveEncoding.storedAlignmentRun_empty_count_bound,
  ``EffectiveEncoding.storedOccupationStepCode_eq,
  ``EffectiveEncoding.storedStageCode_eq,
  ``EffectiveEncoding.storedCompressionCode_eq,
  ``EffectiveEncoding.storedExtractionCode_eq,
  ``EffectiveEncoding.storedSharedRawExtractionCode_eq,
  ``EffectiveEncoding.storedSharedRawExtractionCode_fidelity,
  ``EffectiveEncoding.stageStoredSwapApplications_exact,
  ``EffectiveEncoding.stageStoredSwapApplications_bound,
  ``EffectiveEncoding.extractionStoredSwapApplications_bound
] [
  ``EffectiveEncoding.StoredSwaps,
  ``EffectiveEncoding.applyStoredSwaps,
  ``EffectiveEncoding.storedSwapPermutation,
  ``EffectiveEncoding.StoredAlignmentRun,
  ``EffectiveEncoding.storedAlignmentRun,
  ``EffectiveEncoding.storedOccupationStepCode,
  ``EffectiveEncoding.storedStageCode,
  ``EffectiveEncoding.storedCompressionCode,
  ``EffectiveEncoding.storedExtractionCode,
  ``EffectiveEncoding.storedSharedRawExtractionCode,
  ``EffectiveEncoding.stageStoredSwapApplications,
  ``EffectiveEncoding.extractionStoredSwapApplications
])

#check EffectiveEncoding.applyStoredSwaps_value
#print axioms EffectiveEncoding.applyStoredSwaps_value
#check EffectiveEncoding.applyStoredSwaps_count
#print axioms EffectiveEncoding.applyStoredSwaps_count
#check EffectiveEncoding.storedAlignmentRun_word
#print axioms EffectiveEncoding.storedAlignmentRun_word
#check EffectiveEncoding.storedAlignmentRun_count
#print axioms EffectiveEncoding.storedAlignmentRun_count
#check EffectiveEncoding.storedAlignmentRun_empty_word
#print axioms EffectiveEncoding.storedAlignmentRun_empty_word
#check EffectiveEncoding.storedAlignmentRun_empty_count_bound
#print axioms EffectiveEncoding.storedAlignmentRun_empty_count_bound
#check EffectiveEncoding.storedOccupationStepCode_eq
#print axioms EffectiveEncoding.storedOccupationStepCode_eq
#check EffectiveEncoding.storedStageCode_eq
#print axioms EffectiveEncoding.storedStageCode_eq
#check EffectiveEncoding.storedCompressionCode_eq
#print axioms EffectiveEncoding.storedCompressionCode_eq
#check EffectiveEncoding.storedExtractionCode_eq
#print axioms EffectiveEncoding.storedExtractionCode_eq
#check EffectiveEncoding.storedSharedRawExtractionCode_eq
#print axioms EffectiveEncoding.storedSharedRawExtractionCode_eq
#check EffectiveEncoding.storedSharedRawExtractionCode_fidelity
#print axioms EffectiveEncoding.storedSharedRawExtractionCode_fidelity
#check EffectiveEncoding.stageStoredSwapApplications_exact
#print axioms EffectiveEncoding.stageStoredSwapApplications_exact
#check EffectiveEncoding.stageStoredSwapApplications_bound
#print axioms EffectiveEncoding.stageStoredSwapApplications_bound
#check EffectiveEncoding.extractionStoredSwapApplications_bound
#print axioms EffectiveEncoding.extractionStoredSwapApplications_bound
#check EffectiveEncoding.StoredSwaps
#print axioms EffectiveEncoding.StoredSwaps
#check EffectiveEncoding.applyStoredSwaps
#print axioms EffectiveEncoding.applyStoredSwaps
#check EffectiveEncoding.storedSwapPermutation
#print axioms EffectiveEncoding.storedSwapPermutation
#check EffectiveEncoding.StoredAlignmentRun
#print axioms EffectiveEncoding.StoredAlignmentRun
#check EffectiveEncoding.storedAlignmentRun
#print axioms EffectiveEncoding.storedAlignmentRun
#check EffectiveEncoding.storedOccupationStepCode
#print axioms EffectiveEncoding.storedOccupationStepCode
#check EffectiveEncoding.storedStageCode
#print axioms EffectiveEncoding.storedStageCode
#check EffectiveEncoding.storedCompressionCode
#print axioms EffectiveEncoding.storedCompressionCode
#check EffectiveEncoding.storedExtractionCode
#print axioms EffectiveEncoding.storedExtractionCode
#check EffectiveEncoding.storedSharedRawExtractionCode
#print axioms EffectiveEncoding.storedSharedRawExtractionCode
#check EffectiveEncoding.stageStoredSwapApplications
#print axioms EffectiveEncoding.stageStoredSwapApplications
#check EffectiveEncoding.extractionStoredSwapApplications
#print axioms EffectiveEncoding.extractionStoredSwapApplications
