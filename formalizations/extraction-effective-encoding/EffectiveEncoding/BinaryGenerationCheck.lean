import EffectiveEncoding.BinaryNativeExtraction
import EffectiveEncoding.BinaryGenerationEvaluation

open Lean Elab Command
namespace EffectiveEncodingBinaryGenerationVerification

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

end EffectiveEncodingBinaryGenerationVerification

run_cmd (EffectiveEncodingBinaryGenerationVerification.checkKinds [
  ``EffectiveEncoding.binaryRankProgramsActions_append,
  ``EffectiveEncoding.binaryRankProgramsActions_flatMap,
  ``EffectiveEncoding.binaryNativeBranchEndpoint_endpoint,
  ``EffectiveEncoding.binaryNativeBranchEndpoint_encodingActions,
  ``EffectiveEncoding.binaryNativeNextEndpoint_endpoint,
  ``EffectiveEncoding.binaryNativeNextEndpoint_encodingActions,
  ``EffectiveEncoding.binaryNativePivotEndpoint_endpoint,
  ``EffectiveEncoding.binaryNativePivotEndpoint_encodingActions,
  ``EffectiveEncoding.binaryEndpointMassActions_bound,
  ``EffectiveEncoding.binaryIndexedRun_result,
  ``EffectiveEncoding.binaryIndexedRun_encodingActions,
  ``EffectiveEncoding.binaryNativeBranchRun_result,
  ``EffectiveEncoding.binaryNativeBranchRun_encodingActions,
  ``EffectiveEncoding.binaryAlignmentRun_result,
  ``EffectiveEncoding.binaryAlignmentRun_encodingActions,
  ``EffectiveEncoding.binaryNativeBranchTableRun_result,
  ``EffectiveEncoding.binaryNativeBranchTableRun_encodingActions,
  ``EffectiveEncoding.binaryNativeOccupationRun_result,
  ``EffectiveEncoding.binaryNativeOccupationRun_encodingActions,
  ``EffectiveEncoding.binaryNativeStageRun_result,
  ``EffectiveEncoding.binaryNativeCompressionRun_result,
  ``EffectiveEncoding.binaryNativeCompressionRun_encodingActions,
  ``EffectiveEncoding.binaryNativeDescriptorRun_result,
  ``EffectiveEncoding.binaryNativeDescriptorRun_encodingActions,
  ``EffectiveEncoding.binaryNativeExtractionRun_erase,
  ``EffectiveEncoding.binaryNativeExtractionRun_word,
  ``EffectiveEncoding.binaryNativeExtractionRun_encodingActions,
  ``EffectiveEncoding.binaryNativeExtractionRun_accountedPrimitiveActions,
  ``EffectiveEncoding.binaryNativeExtractionRun_fidelity
] [
  ``EffectiveEncoding.BinaryRankProgramRecord,
  ``EffectiveEncoding.binaryRankProgramsActions,
  ``EffectiveEncoding.BinaryEncodedEndpoint,
  ``EffectiveEncoding.BinaryEncodedEndpoint.encodingActions,
  ``EffectiveEncoding.binaryNativeBranchEndpoint,
  ``EffectiveEncoding.binaryNativeNextEndpoint,
  ``EffectiveEncoding.binaryNativePivotEndpoint,
  ``EffectiveEncoding.BinaryGeneratedRun,
  ``EffectiveEncoding.BinaryGeneratedRun.encodingActions,
  ``EffectiveEncoding.binaryIndexedRun,
  ``EffectiveEncoding.binaryNativeBranchRun,
  ``EffectiveEncoding.BinaryAlignmentResult,
  ``EffectiveEncoding.BinaryAlignmentResult.encodingActions,
  ``EffectiveEncoding.binaryAlignmentRun,
  ``EffectiveEncoding.binaryNativeBranchTableRun,
  ``EffectiveEncoding.binaryNativeOccupationRun,
  ``EffectiveEncoding.binaryNativeStageRun,
  ``EffectiveEncoding.binaryNativeCompressionRun,
  ``EffectiveEncoding.binaryNativeDescriptorRun,
  ``EffectiveEncoding.BinaryNativeExtractionResult,
  ``EffectiveEncoding.BinaryNativeExtractionResult.erase,
  ``EffectiveEncoding.binaryNativeExtractionRun,
  ``EffectiveEncoding.BinaryNativeExtractionResult.accountedPrimitiveActions
])

#check EffectiveEncoding.binaryRankProgramsActions_append
#print axioms EffectiveEncoding.binaryRankProgramsActions_append
#check EffectiveEncoding.binaryRankProgramsActions_flatMap
#print axioms EffectiveEncoding.binaryRankProgramsActions_flatMap
#check EffectiveEncoding.binaryNativeBranchEndpoint_endpoint
#print axioms EffectiveEncoding.binaryNativeBranchEndpoint_endpoint
#check EffectiveEncoding.binaryNativeBranchEndpoint_encodingActions
#print axioms EffectiveEncoding.binaryNativeBranchEndpoint_encodingActions
#check EffectiveEncoding.binaryNativeNextEndpoint_endpoint
#print axioms EffectiveEncoding.binaryNativeNextEndpoint_endpoint
#check EffectiveEncoding.binaryNativeNextEndpoint_encodingActions
#print axioms EffectiveEncoding.binaryNativeNextEndpoint_encodingActions
#check EffectiveEncoding.binaryNativePivotEndpoint_endpoint
#print axioms EffectiveEncoding.binaryNativePivotEndpoint_endpoint
#check EffectiveEncoding.binaryNativePivotEndpoint_encodingActions
#print axioms EffectiveEncoding.binaryNativePivotEndpoint_encodingActions
#check EffectiveEncoding.binaryEndpointMassActions_bound
#print axioms EffectiveEncoding.binaryEndpointMassActions_bound
#check EffectiveEncoding.binaryIndexedRun_result
#print axioms EffectiveEncoding.binaryIndexedRun_result
#check EffectiveEncoding.binaryIndexedRun_encodingActions
#print axioms EffectiveEncoding.binaryIndexedRun_encodingActions
#check EffectiveEncoding.binaryNativeBranchRun_result
#print axioms EffectiveEncoding.binaryNativeBranchRun_result
#check EffectiveEncoding.binaryNativeBranchRun_encodingActions
#print axioms EffectiveEncoding.binaryNativeBranchRun_encodingActions
#check EffectiveEncoding.binaryAlignmentRun_result
#print axioms EffectiveEncoding.binaryAlignmentRun_result
#check EffectiveEncoding.binaryAlignmentRun_encodingActions
#print axioms EffectiveEncoding.binaryAlignmentRun_encodingActions
#check EffectiveEncoding.binaryNativeBranchTableRun_result
#print axioms EffectiveEncoding.binaryNativeBranchTableRun_result
#check EffectiveEncoding.binaryNativeBranchTableRun_encodingActions
#print axioms EffectiveEncoding.binaryNativeBranchTableRun_encodingActions
#check EffectiveEncoding.binaryNativeOccupationRun_result
#print axioms EffectiveEncoding.binaryNativeOccupationRun_result
#check EffectiveEncoding.binaryNativeOccupationRun_encodingActions
#print axioms EffectiveEncoding.binaryNativeOccupationRun_encodingActions
#check EffectiveEncoding.binaryNativeStageRun_result
#print axioms EffectiveEncoding.binaryNativeStageRun_result
#check EffectiveEncoding.binaryNativeCompressionRun_result
#print axioms EffectiveEncoding.binaryNativeCompressionRun_result
#check EffectiveEncoding.binaryNativeCompressionRun_encodingActions
#print axioms EffectiveEncoding.binaryNativeCompressionRun_encodingActions
#check EffectiveEncoding.binaryNativeDescriptorRun_result
#print axioms EffectiveEncoding.binaryNativeDescriptorRun_result
#check EffectiveEncoding.binaryNativeDescriptorRun_encodingActions
#print axioms EffectiveEncoding.binaryNativeDescriptorRun_encodingActions
#check EffectiveEncoding.binaryNativeExtractionRun_erase
#print axioms EffectiveEncoding.binaryNativeExtractionRun_erase
#check EffectiveEncoding.binaryNativeExtractionRun_word
#print axioms EffectiveEncoding.binaryNativeExtractionRun_word
#check EffectiveEncoding.binaryNativeExtractionRun_encodingActions
#print axioms EffectiveEncoding.binaryNativeExtractionRun_encodingActions
#check EffectiveEncoding.binaryNativeExtractionRun_accountedPrimitiveActions
#print axioms EffectiveEncoding.binaryNativeExtractionRun_accountedPrimitiveActions
#check EffectiveEncoding.binaryNativeExtractionRun_fidelity
#print axioms EffectiveEncoding.binaryNativeExtractionRun_fidelity
#check EffectiveEncoding.BinaryRankProgramRecord
#print axioms EffectiveEncoding.BinaryRankProgramRecord
#check EffectiveEncoding.binaryRankProgramsActions
#print axioms EffectiveEncoding.binaryRankProgramsActions
#check EffectiveEncoding.BinaryEncodedEndpoint
#print axioms EffectiveEncoding.BinaryEncodedEndpoint
#check EffectiveEncoding.BinaryEncodedEndpoint.encodingActions
#print axioms EffectiveEncoding.BinaryEncodedEndpoint.encodingActions
#check EffectiveEncoding.binaryNativeBranchEndpoint
#print axioms EffectiveEncoding.binaryNativeBranchEndpoint
#check EffectiveEncoding.binaryNativeNextEndpoint
#print axioms EffectiveEncoding.binaryNativeNextEndpoint
#check EffectiveEncoding.binaryNativePivotEndpoint
#print axioms EffectiveEncoding.binaryNativePivotEndpoint
#check EffectiveEncoding.BinaryGeneratedRun
#print axioms EffectiveEncoding.BinaryGeneratedRun
#check EffectiveEncoding.BinaryGeneratedRun.encodingActions
#print axioms EffectiveEncoding.BinaryGeneratedRun.encodingActions
#check EffectiveEncoding.binaryIndexedRun
#print axioms EffectiveEncoding.binaryIndexedRun
#check EffectiveEncoding.binaryNativeBranchRun
#print axioms EffectiveEncoding.binaryNativeBranchRun
#check EffectiveEncoding.BinaryAlignmentResult
#print axioms EffectiveEncoding.BinaryAlignmentResult
#check EffectiveEncoding.BinaryAlignmentResult.encodingActions
#print axioms EffectiveEncoding.BinaryAlignmentResult.encodingActions
#check EffectiveEncoding.binaryAlignmentRun
#print axioms EffectiveEncoding.binaryAlignmentRun
#check EffectiveEncoding.binaryNativeBranchTableRun
#print axioms EffectiveEncoding.binaryNativeBranchTableRun
#check EffectiveEncoding.binaryNativeOccupationRun
#print axioms EffectiveEncoding.binaryNativeOccupationRun
#check EffectiveEncoding.binaryNativeStageRun
#print axioms EffectiveEncoding.binaryNativeStageRun
#check EffectiveEncoding.binaryNativeCompressionRun
#print axioms EffectiveEncoding.binaryNativeCompressionRun
#check EffectiveEncoding.binaryNativeDescriptorRun
#print axioms EffectiveEncoding.binaryNativeDescriptorRun
#check EffectiveEncoding.BinaryNativeExtractionResult
#print axioms EffectiveEncoding.BinaryNativeExtractionResult
#check EffectiveEncoding.BinaryNativeExtractionResult.erase
#print axioms EffectiveEncoding.BinaryNativeExtractionResult.erase
#check EffectiveEncoding.binaryNativeExtractionRun
#print axioms EffectiveEncoding.binaryNativeExtractionRun
#check EffectiveEncoding.BinaryNativeExtractionResult.accountedPrimitiveActions
#print axioms EffectiveEncoding.BinaryNativeExtractionResult.accountedPrimitiveActions
