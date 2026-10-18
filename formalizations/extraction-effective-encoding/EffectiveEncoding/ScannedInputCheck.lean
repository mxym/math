import EffectiveEncoding.FullyScannedInputExtraction
import EffectiveEncoding.ScannedInputEvaluation

open Lean Elab Command
namespace EffectiveEncodingScannedInputVerification

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

end EffectiveEncodingScannedInputVerification

run_cmd (EffectiveEncodingScannedInputVerification.checkKinds [
  ``EffectiveEncoding.booleanRankRecordsActions_append,
  ``EffectiveEncoding.scannedRankWordProgram_word,
  ``EffectiveEncoding.scannedNativeBranchEndpoint_binary,
  ``EffectiveEncoding.scannedNativeBranchEndpoint_scanActions,
  ``EffectiveEncoding.scannedNativeNextEndpoint_binary,
  ``EffectiveEncoding.scannedNativeNextEndpoint_scanActions,
  ``EffectiveEncoding.scannedNativePivotEndpoint_binary,
  ``EffectiveEncoding.scannedNativePivotEndpoint_scanActions,
  ``EffectiveEncoding.scannedEndpointMassActions_bound,
  ``EffectiveEncoding.scannedIndexedRun_result,
  ``EffectiveEncoding.scannedIndexedRun_scanActions,
  ``EffectiveEncoding.scannedNativeBranchRun_result,
  ``EffectiveEncoding.scannedNativeBranchRun_scanActions,
  ``EffectiveEncoding.scannedAlignmentRun_result,
  ``EffectiveEncoding.scannedAlignmentRun_scanActions,
  ``EffectiveEncoding.scannedNativeBranchTableRun_result,
  ``EffectiveEncoding.scannedNativeBranchTableRun_scanActions,
  ``EffectiveEncoding.scannedNativeOccupationRun_result,
  ``EffectiveEncoding.scannedNativeOccupationRun_scanActions,
  ``EffectiveEncoding.scannedNativeStageRun_result,
  ``EffectiveEncoding.scannedNativeCompressionRun_result,
  ``EffectiveEncoding.scannedNativeCompressionRun_scanActions,
  ``EffectiveEncoding.scannedNativeDescriptorRun_result,
  ``EffectiveEncoding.scannedNativeDescriptorRun_scanActions,
  ``EffectiveEncoding.fullyScannedInputRun_erase,
  ``EffectiveEncoding.fullyScannedInputRun_word,
  ``EffectiveEncoding.fullyScannedInputRun_scanActions,
  ``EffectiveEncoding.fullyScannedInputRun_accountedPrimitiveActions,
  ``EffectiveEncoding.fullyScannedInputRun_fidelity
] [
  ``EffectiveEncoding.BooleanRankRecord,
  ``EffectiveEncoding.booleanRankRecordsActions,
  ``EffectiveEncoding.ScannedRankWord,
  ``EffectiveEncoding.scannedRankWordProgram,
  ``EffectiveEncoding.ScannedEncodedEndpoint,
  ``EffectiveEncoding.ScannedEncodedEndpoint.scanActions,
  ``EffectiveEncoding.scannedNativeBranchEndpoint,
  ``EffectiveEncoding.scannedNativeNextEndpoint,
  ``EffectiveEncoding.scannedNativePivotEndpoint,
  ``EffectiveEncoding.ScannedGeneratedRun,
  ``EffectiveEncoding.ScannedGeneratedRun.scanActions,
  ``EffectiveEncoding.scannedIndexedRun,
  ``EffectiveEncoding.scannedNativeBranchRun,
  ``EffectiveEncoding.ScannedAlignmentResult,
  ``EffectiveEncoding.ScannedAlignmentResult.scanActions,
  ``EffectiveEncoding.scannedAlignmentRun,
  ``EffectiveEncoding.scannedNativeBranchTableRun,
  ``EffectiveEncoding.scannedNativeOccupationRun,
  ``EffectiveEncoding.scannedNativeStageRun,
  ``EffectiveEncoding.scannedNativeCompressionRun,
  ``EffectiveEncoding.scannedNativeDescriptorRun,
  ``EffectiveEncoding.FullyScannedInputResult,
  ``EffectiveEncoding.FullyScannedInputResult.erase,
  ``EffectiveEncoding.fullyScannedInputRun,
  ``EffectiveEncoding.FullyScannedInputResult.accountedPrimitiveActions
])

#check EffectiveEncoding.booleanRankRecordsActions_append
#print axioms EffectiveEncoding.booleanRankRecordsActions_append
#check EffectiveEncoding.scannedRankWordProgram_word
#print axioms EffectiveEncoding.scannedRankWordProgram_word
#check EffectiveEncoding.scannedNativeBranchEndpoint_binary
#print axioms EffectiveEncoding.scannedNativeBranchEndpoint_binary
#check EffectiveEncoding.scannedNativeBranchEndpoint_scanActions
#print axioms EffectiveEncoding.scannedNativeBranchEndpoint_scanActions
#check EffectiveEncoding.scannedNativeNextEndpoint_binary
#print axioms EffectiveEncoding.scannedNativeNextEndpoint_binary
#check EffectiveEncoding.scannedNativeNextEndpoint_scanActions
#print axioms EffectiveEncoding.scannedNativeNextEndpoint_scanActions
#check EffectiveEncoding.scannedNativePivotEndpoint_binary
#print axioms EffectiveEncoding.scannedNativePivotEndpoint_binary
#check EffectiveEncoding.scannedNativePivotEndpoint_scanActions
#print axioms EffectiveEncoding.scannedNativePivotEndpoint_scanActions
#check EffectiveEncoding.scannedEndpointMassActions_bound
#print axioms EffectiveEncoding.scannedEndpointMassActions_bound
#check EffectiveEncoding.scannedIndexedRun_result
#print axioms EffectiveEncoding.scannedIndexedRun_result
#check EffectiveEncoding.scannedIndexedRun_scanActions
#print axioms EffectiveEncoding.scannedIndexedRun_scanActions
#check EffectiveEncoding.scannedNativeBranchRun_result
#print axioms EffectiveEncoding.scannedNativeBranchRun_result
#check EffectiveEncoding.scannedNativeBranchRun_scanActions
#print axioms EffectiveEncoding.scannedNativeBranchRun_scanActions
#check EffectiveEncoding.scannedAlignmentRun_result
#print axioms EffectiveEncoding.scannedAlignmentRun_result
#check EffectiveEncoding.scannedAlignmentRun_scanActions
#print axioms EffectiveEncoding.scannedAlignmentRun_scanActions
#check EffectiveEncoding.scannedNativeBranchTableRun_result
#print axioms EffectiveEncoding.scannedNativeBranchTableRun_result
#check EffectiveEncoding.scannedNativeBranchTableRun_scanActions
#print axioms EffectiveEncoding.scannedNativeBranchTableRun_scanActions
#check EffectiveEncoding.scannedNativeOccupationRun_result
#print axioms EffectiveEncoding.scannedNativeOccupationRun_result
#check EffectiveEncoding.scannedNativeOccupationRun_scanActions
#print axioms EffectiveEncoding.scannedNativeOccupationRun_scanActions
#check EffectiveEncoding.scannedNativeStageRun_result
#print axioms EffectiveEncoding.scannedNativeStageRun_result
#check EffectiveEncoding.scannedNativeCompressionRun_result
#print axioms EffectiveEncoding.scannedNativeCompressionRun_result
#check EffectiveEncoding.scannedNativeCompressionRun_scanActions
#print axioms EffectiveEncoding.scannedNativeCompressionRun_scanActions
#check EffectiveEncoding.scannedNativeDescriptorRun_result
#print axioms EffectiveEncoding.scannedNativeDescriptorRun_result
#check EffectiveEncoding.scannedNativeDescriptorRun_scanActions
#print axioms EffectiveEncoding.scannedNativeDescriptorRun_scanActions
#check EffectiveEncoding.fullyScannedInputRun_erase
#print axioms EffectiveEncoding.fullyScannedInputRun_erase
#check EffectiveEncoding.fullyScannedInputRun_word
#print axioms EffectiveEncoding.fullyScannedInputRun_word
#check EffectiveEncoding.fullyScannedInputRun_scanActions
#print axioms EffectiveEncoding.fullyScannedInputRun_scanActions
#check EffectiveEncoding.fullyScannedInputRun_accountedPrimitiveActions
#print axioms EffectiveEncoding.fullyScannedInputRun_accountedPrimitiveActions
#check EffectiveEncoding.fullyScannedInputRun_fidelity
#print axioms EffectiveEncoding.fullyScannedInputRun_fidelity
#check EffectiveEncoding.BooleanRankRecord
#print axioms EffectiveEncoding.BooleanRankRecord
#check EffectiveEncoding.booleanRankRecordsActions
#print axioms EffectiveEncoding.booleanRankRecordsActions
#check EffectiveEncoding.ScannedRankWord
#print axioms EffectiveEncoding.ScannedRankWord
#check EffectiveEncoding.scannedRankWordProgram
#print axioms EffectiveEncoding.scannedRankWordProgram
#check EffectiveEncoding.ScannedEncodedEndpoint
#print axioms EffectiveEncoding.ScannedEncodedEndpoint
#check EffectiveEncoding.ScannedEncodedEndpoint.scanActions
#print axioms EffectiveEncoding.ScannedEncodedEndpoint.scanActions
#check EffectiveEncoding.scannedNativeBranchEndpoint
#print axioms EffectiveEncoding.scannedNativeBranchEndpoint
#check EffectiveEncoding.scannedNativeNextEndpoint
#print axioms EffectiveEncoding.scannedNativeNextEndpoint
#check EffectiveEncoding.scannedNativePivotEndpoint
#print axioms EffectiveEncoding.scannedNativePivotEndpoint
#check EffectiveEncoding.ScannedGeneratedRun
#print axioms EffectiveEncoding.ScannedGeneratedRun
#check EffectiveEncoding.ScannedGeneratedRun.scanActions
#print axioms EffectiveEncoding.ScannedGeneratedRun.scanActions
#check EffectiveEncoding.scannedIndexedRun
#print axioms EffectiveEncoding.scannedIndexedRun
#check EffectiveEncoding.scannedNativeBranchRun
#print axioms EffectiveEncoding.scannedNativeBranchRun
#check EffectiveEncoding.ScannedAlignmentResult
#print axioms EffectiveEncoding.ScannedAlignmentResult
#check EffectiveEncoding.ScannedAlignmentResult.scanActions
#print axioms EffectiveEncoding.ScannedAlignmentResult.scanActions
#check EffectiveEncoding.scannedAlignmentRun
#print axioms EffectiveEncoding.scannedAlignmentRun
#check EffectiveEncoding.scannedNativeBranchTableRun
#print axioms EffectiveEncoding.scannedNativeBranchTableRun
#check EffectiveEncoding.scannedNativeOccupationRun
#print axioms EffectiveEncoding.scannedNativeOccupationRun
#check EffectiveEncoding.scannedNativeStageRun
#print axioms EffectiveEncoding.scannedNativeStageRun
#check EffectiveEncoding.scannedNativeCompressionRun
#print axioms EffectiveEncoding.scannedNativeCompressionRun
#check EffectiveEncoding.scannedNativeDescriptorRun
#print axioms EffectiveEncoding.scannedNativeDescriptorRun
#check EffectiveEncoding.FullyScannedInputResult
#print axioms EffectiveEncoding.FullyScannedInputResult
#check EffectiveEncoding.FullyScannedInputResult.erase
#print axioms EffectiveEncoding.FullyScannedInputResult.erase
#check EffectiveEncoding.fullyScannedInputRun
#print axioms EffectiveEncoding.fullyScannedInputRun
#check EffectiveEncoding.FullyScannedInputResult.accountedPrimitiveActions
#print axioms EffectiveEncoding.FullyScannedInputResult.accountedPrimitiveActions
