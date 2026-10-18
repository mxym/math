import EffectiveEncoding.PreparedNativeExtraction
import EffectiveEncoding.PreparedPauliEvaluation

open Lean Elab Command
namespace EffectiveEncodingPreparedNativeVerification

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

end EffectiveEncodingPreparedNativeVerification

run_cmd (EffectiveEncodingPreparedNativeVerification.checkKinds [
  ``EffectiveEncoding.runPreparedPauli_eq,
  ``EffectiveEncoding.preparedParity_eq,
  ``EffectiveEncoding.preparedSelectedCode_eq,
  ``EffectiveEncoding.preparedMaskTable_length,
  ``EffectiveEncoding.preparePauliPlan_payloadCells,
  ``EffectiveEncoding.preparedMaskTablePayload_bound,
  ``EffectiveEncoding.preparedAdjacentSwapCode_eq,
  ``EffectiveEncoding.preparedAdjacentRotationCode_eq,
  ``EffectiveEncoding.preparedOrientedRotationCode_eq,
  ``EffectiveEncoding.preparedMoveCode_eq,
  ``EffectiveEncoding.preparedSwapCode_eq,
  ``EffectiveEncoding.preparedRotationCode_eq,
  ``EffectiveEncoding.preparedRawCompile_eq,
  ``EffectiveEncoding.preparedCompileRaw_eq,
  ``EffectiveEncoding.preparedIndexedRun_eq,
  ``EffectiveEncoding.preparedRankedAlignmentRun_eq,
  ``EffectiveEncoding.preparedNativeBranchRun_eq,
  ``EffectiveEncoding.preparedNativeBranchTableRun_eq,
  ``EffectiveEncoding.preparedNativeOccupationRun_eq,
  ``EffectiveEncoding.preparedNativeStageRun_eq,
  ``EffectiveEncoding.preparedNativeCompressionRun_eq,
  ``EffectiveEncoding.preparedNativeDescriptorRun_eq,
  ``EffectiveEncoding.nativeActiveWires_eq,
  ``EffectiveEncoding.activePreparedMaskPayload,
  ``EffectiveEncoding.preparedNativeBooleanExtractionRun_eq,
  ``EffectiveEncoding.preparedNativeBooleanExtractionRun_onlineActions,
  ``EffectiveEncoding.preparedNativeBooleanExtractionRun_providerRootCharge,
  ``EffectiveEncoding.preparedNativeBooleanExtractionRun_fidelity,
  ``EffectiveEncoding.totalPreparedMaskPayload_bound
] [
  ``EffectiveEncoding.PreparedPauliPlan,
  ``EffectiveEncoding.preparePauliPlan,
  ``EffectiveEncoding.runPreparedPauli,
  ``EffectiveEncoding.preparedParity,
  ``EffectiveEncoding.preparedMaskTable,
  ``EffectiveEncoding.preparedSelectedCode,
  ``EffectiveEncoding.PreparedPauliPlan.payloadCells,
  ``EffectiveEncoding.preparedMaskTablePayload,
  ``EffectiveEncoding.preparedAdjacentSwapCode,
  ``EffectiveEncoding.preparedAdjacentRotationCode,
  ``EffectiveEncoding.preparedOrientedRotationCode,
  ``EffectiveEncoding.preparedMoveCode,
  ``EffectiveEncoding.preparedSwapCode,
  ``EffectiveEncoding.preparedRotationCode,
  ``EffectiveEncoding.preparedRawCompile,
  ``EffectiveEncoding.preparedCompileRaw,
  ``EffectiveEncoding.preparedIndexedRun,
  ``EffectiveEncoding.preparedRankedAlignmentRun,
  ``EffectiveEncoding.preparedNativeBranchRun,
  ``EffectiveEncoding.preparedNativeBranchTableRun,
  ``EffectiveEncoding.preparedNativeOccupationRun,
  ``EffectiveEncoding.preparedNativeStageRun,
  ``EffectiveEncoding.preparedNativeCompressionRun,
  ``EffectiveEncoding.preparedNativeDescriptorRun,
  ``EffectiveEncoding.preparedNativeBooleanExtractionRun,
  ``EffectiveEncoding.totalPreparedMaskPayload
])

#check EffectiveEncoding.runPreparedPauli_eq
#print axioms EffectiveEncoding.runPreparedPauli_eq
#check EffectiveEncoding.preparedParity_eq
#print axioms EffectiveEncoding.preparedParity_eq
#check EffectiveEncoding.preparedSelectedCode_eq
#print axioms EffectiveEncoding.preparedSelectedCode_eq
#check EffectiveEncoding.preparedMaskTable_length
#print axioms EffectiveEncoding.preparedMaskTable_length
#check EffectiveEncoding.preparePauliPlan_payloadCells
#print axioms EffectiveEncoding.preparePauliPlan_payloadCells
#check EffectiveEncoding.preparedMaskTablePayload_bound
#print axioms EffectiveEncoding.preparedMaskTablePayload_bound
#check EffectiveEncoding.preparedAdjacentSwapCode_eq
#print axioms EffectiveEncoding.preparedAdjacentSwapCode_eq
#check EffectiveEncoding.preparedAdjacentRotationCode_eq
#print axioms EffectiveEncoding.preparedAdjacentRotationCode_eq
#check EffectiveEncoding.preparedOrientedRotationCode_eq
#print axioms EffectiveEncoding.preparedOrientedRotationCode_eq
#check EffectiveEncoding.preparedMoveCode_eq
#print axioms EffectiveEncoding.preparedMoveCode_eq
#check EffectiveEncoding.preparedSwapCode_eq
#print axioms EffectiveEncoding.preparedSwapCode_eq
#check EffectiveEncoding.preparedRotationCode_eq
#print axioms EffectiveEncoding.preparedRotationCode_eq
#check EffectiveEncoding.preparedRawCompile_eq
#print axioms EffectiveEncoding.preparedRawCompile_eq
#check EffectiveEncoding.preparedCompileRaw_eq
#print axioms EffectiveEncoding.preparedCompileRaw_eq
#check EffectiveEncoding.preparedIndexedRun_eq
#print axioms EffectiveEncoding.preparedIndexedRun_eq
#check EffectiveEncoding.preparedRankedAlignmentRun_eq
#print axioms EffectiveEncoding.preparedRankedAlignmentRun_eq
#check EffectiveEncoding.preparedNativeBranchRun_eq
#print axioms EffectiveEncoding.preparedNativeBranchRun_eq
#check EffectiveEncoding.preparedNativeBranchTableRun_eq
#print axioms EffectiveEncoding.preparedNativeBranchTableRun_eq
#check EffectiveEncoding.preparedNativeOccupationRun_eq
#print axioms EffectiveEncoding.preparedNativeOccupationRun_eq
#check EffectiveEncoding.preparedNativeStageRun_eq
#print axioms EffectiveEncoding.preparedNativeStageRun_eq
#check EffectiveEncoding.preparedNativeCompressionRun_eq
#print axioms EffectiveEncoding.preparedNativeCompressionRun_eq
#check EffectiveEncoding.preparedNativeDescriptorRun_eq
#print axioms EffectiveEncoding.preparedNativeDescriptorRun_eq
#check EffectiveEncoding.nativeActiveWires_eq
#print axioms EffectiveEncoding.nativeActiveWires_eq
#check EffectiveEncoding.activePreparedMaskPayload
#print axioms EffectiveEncoding.activePreparedMaskPayload
#check EffectiveEncoding.preparedNativeBooleanExtractionRun_eq
#print axioms EffectiveEncoding.preparedNativeBooleanExtractionRun_eq
#check EffectiveEncoding.preparedNativeBooleanExtractionRun_onlineActions
#print axioms EffectiveEncoding.preparedNativeBooleanExtractionRun_onlineActions
#check EffectiveEncoding.preparedNativeBooleanExtractionRun_providerRootCharge
#print axioms EffectiveEncoding.preparedNativeBooleanExtractionRun_providerRootCharge
#check EffectiveEncoding.preparedNativeBooleanExtractionRun_fidelity
#print axioms EffectiveEncoding.preparedNativeBooleanExtractionRun_fidelity
#check EffectiveEncoding.totalPreparedMaskPayload_bound
#print axioms EffectiveEncoding.totalPreparedMaskPayload_bound
#check EffectiveEncoding.PreparedPauliPlan
#print axioms EffectiveEncoding.PreparedPauliPlan
#check EffectiveEncoding.preparePauliPlan
#print axioms EffectiveEncoding.preparePauliPlan
#check EffectiveEncoding.runPreparedPauli
#print axioms EffectiveEncoding.runPreparedPauli
#check EffectiveEncoding.preparedParity
#print axioms EffectiveEncoding.preparedParity
#check EffectiveEncoding.preparedMaskTable
#print axioms EffectiveEncoding.preparedMaskTable
#check EffectiveEncoding.preparedSelectedCode
#print axioms EffectiveEncoding.preparedSelectedCode
#check EffectiveEncoding.PreparedPauliPlan.payloadCells
#print axioms EffectiveEncoding.PreparedPauliPlan.payloadCells
#check EffectiveEncoding.preparedMaskTablePayload
#print axioms EffectiveEncoding.preparedMaskTablePayload
#check EffectiveEncoding.preparedAdjacentSwapCode
#print axioms EffectiveEncoding.preparedAdjacentSwapCode
#check EffectiveEncoding.preparedAdjacentRotationCode
#print axioms EffectiveEncoding.preparedAdjacentRotationCode
#check EffectiveEncoding.preparedOrientedRotationCode
#print axioms EffectiveEncoding.preparedOrientedRotationCode
#check EffectiveEncoding.preparedMoveCode
#print axioms EffectiveEncoding.preparedMoveCode
#check EffectiveEncoding.preparedSwapCode
#print axioms EffectiveEncoding.preparedSwapCode
#check EffectiveEncoding.preparedRotationCode
#print axioms EffectiveEncoding.preparedRotationCode
#check EffectiveEncoding.preparedRawCompile
#print axioms EffectiveEncoding.preparedRawCompile
#check EffectiveEncoding.preparedCompileRaw
#print axioms EffectiveEncoding.preparedCompileRaw
#check EffectiveEncoding.preparedIndexedRun
#print axioms EffectiveEncoding.preparedIndexedRun
#check EffectiveEncoding.preparedRankedAlignmentRun
#print axioms EffectiveEncoding.preparedRankedAlignmentRun
#check EffectiveEncoding.preparedNativeBranchRun
#print axioms EffectiveEncoding.preparedNativeBranchRun
#check EffectiveEncoding.preparedNativeBranchTableRun
#print axioms EffectiveEncoding.preparedNativeBranchTableRun
#check EffectiveEncoding.preparedNativeOccupationRun
#print axioms EffectiveEncoding.preparedNativeOccupationRun
#check EffectiveEncoding.preparedNativeStageRun
#print axioms EffectiveEncoding.preparedNativeStageRun
#check EffectiveEncoding.preparedNativeCompressionRun
#print axioms EffectiveEncoding.preparedNativeCompressionRun
#check EffectiveEncoding.preparedNativeDescriptorRun
#print axioms EffectiveEncoding.preparedNativeDescriptorRun
#check EffectiveEncoding.preparedNativeBooleanExtractionRun
#print axioms EffectiveEncoding.preparedNativeBooleanExtractionRun
#check EffectiveEncoding.totalPreparedMaskPayload
#print axioms EffectiveEncoding.totalPreparedMaskPayload
