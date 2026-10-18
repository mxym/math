import EffectiveEncoding.NativeRankExtraction

open Lean Elab Command
namespace EffectiveEncodingNativeRankVerification

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

end EffectiveEncodingNativeRankVerification

run_cmd (EffectiveEncodingNativeRankVerification.checkKinds [
  ``EffectiveEncoding.nativeMass_value,
  ``EffectiveEncoding.nativeSelected_mem,
  ``EffectiveEncoding.nativeSelected_eq,
  ``EffectiveEncoding.nativeOccupiedPivot_eq,
  ``EffectiveEncoding.nativeOccupationTable_values,
  ``EffectiveEncoding.nativeBranchEndpoint_eq,
  ``EffectiveEncoding.nativeNextEndpoint_eq,
  ``EffectiveEncoding.nativePivotEndpoint_eq,
  ``EffectiveEncoding.nativeBranchRun_eq,
  ``EffectiveEncoding.nativeBranchTableRun_eq,
  ``EffectiveEncoding.nativeAlignmentRun_eq,
  ``EffectiveEncoding.nativeOccupationRun_eq,
  ``EffectiveEncoding.nativeStageRun_eq,
  ``EffectiveEncoding.nativeCompressionRun_eq,
  ``EffectiveEncoding.nativeDescriptorRun_eq,
  ``EffectiveEncoding.nativeDescriptorRun_work,
  ``EffectiveEncoding.nativeRankExtractionRun_eq,
  ``EffectiveEncoding.nativeRankExtractionRun_word,
  ``EffectiveEncoding.nativeRankExtractionRun_work,
  ``EffectiveEncoding.nativeRankExtractionRun_fidelity
] [
  ``EffectiveEncoding.NativeOccupation,
  ``EffectiveEncoding.nativeOccupationValue,
  ``EffectiveEncoding.nativeMass,
  ``EffectiveEncoding.nativeSelected,
  ``EffectiveEncoding.nativeOccupiedFintype,
  ``EffectiveEncoding.nativeOccupiedPivot,
  ``EffectiveEncoding.nativeOccupationTable,
  ``EffectiveEncoding.nativeBranchEndpoint,
  ``EffectiveEncoding.nativeNextEndpoint,
  ``EffectiveEncoding.nativePivotEndpoint,
  ``EffectiveEncoding.nativeBranchRun,
  ``EffectiveEncoding.nativeBranchTableRun,
  ``EffectiveEncoding.nativeAlignmentRun,
  ``EffectiveEncoding.nativeOccupationRun,
  ``EffectiveEncoding.nativeStageRun,
  ``EffectiveEncoding.nativeCompressionRun,
  ``EffectiveEncoding.nativeDescriptorRun,
  ``EffectiveEncoding.nativeRankExtractionRun
])

#check EffectiveEncoding.nativeMass_value
#print axioms EffectiveEncoding.nativeMass_value
#check EffectiveEncoding.nativeSelected_mem
#print axioms EffectiveEncoding.nativeSelected_mem
#check EffectiveEncoding.nativeSelected_eq
#print axioms EffectiveEncoding.nativeSelected_eq
#check EffectiveEncoding.nativeOccupiedPivot_eq
#print axioms EffectiveEncoding.nativeOccupiedPivot_eq
#check EffectiveEncoding.nativeOccupationTable_values
#print axioms EffectiveEncoding.nativeOccupationTable_values
#check EffectiveEncoding.nativeBranchEndpoint_eq
#print axioms EffectiveEncoding.nativeBranchEndpoint_eq
#check EffectiveEncoding.nativeNextEndpoint_eq
#print axioms EffectiveEncoding.nativeNextEndpoint_eq
#check EffectiveEncoding.nativePivotEndpoint_eq
#print axioms EffectiveEncoding.nativePivotEndpoint_eq
#check EffectiveEncoding.nativeBranchRun_eq
#print axioms EffectiveEncoding.nativeBranchRun_eq
#check EffectiveEncoding.nativeBranchTableRun_eq
#print axioms EffectiveEncoding.nativeBranchTableRun_eq
#check EffectiveEncoding.nativeAlignmentRun_eq
#print axioms EffectiveEncoding.nativeAlignmentRun_eq
#check EffectiveEncoding.nativeOccupationRun_eq
#print axioms EffectiveEncoding.nativeOccupationRun_eq
#check EffectiveEncoding.nativeStageRun_eq
#print axioms EffectiveEncoding.nativeStageRun_eq
#check EffectiveEncoding.nativeCompressionRun_eq
#print axioms EffectiveEncoding.nativeCompressionRun_eq
#check EffectiveEncoding.nativeDescriptorRun_eq
#print axioms EffectiveEncoding.nativeDescriptorRun_eq
#check EffectiveEncoding.nativeDescriptorRun_work
#print axioms EffectiveEncoding.nativeDescriptorRun_work
#check EffectiveEncoding.nativeRankExtractionRun_eq
#print axioms EffectiveEncoding.nativeRankExtractionRun_eq
#check EffectiveEncoding.nativeRankExtractionRun_word
#print axioms EffectiveEncoding.nativeRankExtractionRun_word
#check EffectiveEncoding.nativeRankExtractionRun_work
#print axioms EffectiveEncoding.nativeRankExtractionRun_work
#check EffectiveEncoding.nativeRankExtractionRun_fidelity
#print axioms EffectiveEncoding.nativeRankExtractionRun_fidelity
#check EffectiveEncoding.NativeOccupation
#print axioms EffectiveEncoding.NativeOccupation
#check EffectiveEncoding.nativeOccupationValue
#print axioms EffectiveEncoding.nativeOccupationValue
#check EffectiveEncoding.nativeMass
#print axioms EffectiveEncoding.nativeMass
#check EffectiveEncoding.nativeSelected
#print axioms EffectiveEncoding.nativeSelected
#check EffectiveEncoding.nativeOccupiedFintype
#print axioms EffectiveEncoding.nativeOccupiedFintype
#check EffectiveEncoding.nativeOccupiedPivot
#print axioms EffectiveEncoding.nativeOccupiedPivot
#check EffectiveEncoding.nativeOccupationTable
#print axioms EffectiveEncoding.nativeOccupationTable
#check EffectiveEncoding.nativeBranchEndpoint
#print axioms EffectiveEncoding.nativeBranchEndpoint
#check EffectiveEncoding.nativeNextEndpoint
#print axioms EffectiveEncoding.nativeNextEndpoint
#check EffectiveEncoding.nativePivotEndpoint
#print axioms EffectiveEncoding.nativePivotEndpoint
#check EffectiveEncoding.nativeBranchRun
#print axioms EffectiveEncoding.nativeBranchRun
#check EffectiveEncoding.nativeBranchTableRun
#print axioms EffectiveEncoding.nativeBranchTableRun
#check EffectiveEncoding.nativeAlignmentRun
#print axioms EffectiveEncoding.nativeAlignmentRun
#check EffectiveEncoding.nativeOccupationRun
#print axioms EffectiveEncoding.nativeOccupationRun
#check EffectiveEncoding.nativeStageRun
#print axioms EffectiveEncoding.nativeStageRun
#check EffectiveEncoding.nativeCompressionRun
#print axioms EffectiveEncoding.nativeCompressionRun
#check EffectiveEncoding.nativeDescriptorRun
#print axioms EffectiveEncoding.nativeDescriptorRun
#check EffectiveEncoding.nativeRankExtractionRun
#print axioms EffectiveEncoding.nativeRankExtractionRun
