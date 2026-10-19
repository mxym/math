import EffectiveEncoding.MaskedSerializedRun
import EffectiveEncoding.BinaryMaskEvaluation

open Lean Elab Command
namespace EffectiveEncodingBinaryMaskVerification

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

end EffectiveEncodingBinaryMaskVerification

run_cmd (EffectiveEncodingBinaryMaskVerification.checkKinds [
  ``EffectiveEncoding.endpointBitsProgram_unary_exact,
  ``EffectiveEncoding.naturalRange_map_ofFn,
  ``EffectiveEncoding.binaryMaskPlanProgram_outputs,
  ``EffectiveEncoding.binaryMaskPlanProgram_plans,
  ``EffectiveEncoding.binaryMaskPlanProgram_length,
  ``EffectiveEncoding.endpointBitsMap_actions,
  ``EffectiveEncoding.binaryMaskPlanProgram_copyActions,
  ``EffectiveEncoding.binaryMaskPlanProgram_actions,
  ``EffectiveEncoding.binaryMaskPlanProgram_active_actions,
  ``EffectiveEncoding.maskedCandidateOccupationRun_generation,
  ``EffectiveEncoding.maskedCandidateOccupationRun_maskActions,
  ``EffectiveEncoding.maskedCandidateStageRun_generation,
  ``EffectiveEncoding.maskedCandidateCompressionRun_generation,
  ``EffectiveEncoding.maskedCandidateCompressionRun_maskActions,
  ``EffectiveEncoding.maskedCandidateDescriptorRun_generation,
  ``EffectiveEncoding.maskedCandidateDescriptorRun_word,
  ``EffectiveEncoding.maskedCandidateDescriptorRun_maskActions,
  ``EffectiveEncoding.maskedCandidateDescriptorRun_accountedActions,
  ``EffectiveEncoding.maskedCandidateDescriptorRun_accountedActions_polynomial,
  ``EffectiveEncoding.maskedSerializedRun_execution,
  ``EffectiveEncoding.maskedSerializedRun_suffix_roundtrip,
  ``EffectiveEncoding.maskedSerializedRun_decoded_word,
  ``EffectiveEncoding.maskedSerializedRun_maskActions,
  ``EffectiveEncoding.maskedGeneration_uniform,
  ``EffectiveEncoding.maskedSerializedRun_accountedPrimitiveActions_polynomial,
  ``EffectiveEncoding.maskedSerializedRun_fidelity
] [
  ``EffectiveEncoding.BinaryMaskPlanResult,
  ``EffectiveEncoding.binaryMaskPlanProgram,
  ``EffectiveEncoding.BinaryMaskPlanResult.copyActions,
  ``EffectiveEncoding.BinaryMaskPlanResult.actions,
  ``EffectiveEncoding.BinaryMaskRecord,
  ``EffectiveEncoding.MaskedCandidateResult,
  ``EffectiveEncoding.maskedCandidateOccupationRun,
  ``EffectiveEncoding.MaskedCandidateResult.maskActions,
  ``EffectiveEncoding.maskedCandidateStageRun,
  ``EffectiveEncoding.maskedCandidateCompressionRun,
  ``EffectiveEncoding.maskedCandidateDescriptorRun,
  ``EffectiveEncoding.MaskedCandidateResult.accountedActions,
  ``EffectiveEncoding.MaskedSerializedResult,
  ``EffectiveEncoding.maskedSerializedRun,
  ``EffectiveEncoding.MaskedSerializedResult.decoded,
  ``EffectiveEncoding.MaskedSerializedResult.maskActions,
  ``EffectiveEncoding.MaskedSerializedResult.accountedPrimitiveActions,
  ``EffectiveEncoding.maskedSerializedPolynomialConstant
])

#check EffectiveEncoding.endpointBitsProgram_unary_exact
#print axioms EffectiveEncoding.endpointBitsProgram_unary_exact
#check EffectiveEncoding.naturalRange_map_ofFn
#print axioms EffectiveEncoding.naturalRange_map_ofFn
#check EffectiveEncoding.binaryMaskPlanProgram_outputs
#print axioms EffectiveEncoding.binaryMaskPlanProgram_outputs
#check EffectiveEncoding.binaryMaskPlanProgram_plans
#print axioms EffectiveEncoding.binaryMaskPlanProgram_plans
#check EffectiveEncoding.binaryMaskPlanProgram_length
#print axioms EffectiveEncoding.binaryMaskPlanProgram_length
#check EffectiveEncoding.endpointBitsMap_actions
#print axioms EffectiveEncoding.endpointBitsMap_actions
#check EffectiveEncoding.binaryMaskPlanProgram_copyActions
#print axioms EffectiveEncoding.binaryMaskPlanProgram_copyActions
#check EffectiveEncoding.binaryMaskPlanProgram_actions
#print axioms EffectiveEncoding.binaryMaskPlanProgram_actions
#check EffectiveEncoding.binaryMaskPlanProgram_active_actions
#print axioms EffectiveEncoding.binaryMaskPlanProgram_active_actions
#check EffectiveEncoding.maskedCandidateOccupationRun_generation
#print axioms EffectiveEncoding.maskedCandidateOccupationRun_generation
#check EffectiveEncoding.maskedCandidateOccupationRun_maskActions
#print axioms EffectiveEncoding.maskedCandidateOccupationRun_maskActions
#check EffectiveEncoding.maskedCandidateStageRun_generation
#print axioms EffectiveEncoding.maskedCandidateStageRun_generation
#check EffectiveEncoding.maskedCandidateCompressionRun_generation
#print axioms EffectiveEncoding.maskedCandidateCompressionRun_generation
#check EffectiveEncoding.maskedCandidateCompressionRun_maskActions
#print axioms EffectiveEncoding.maskedCandidateCompressionRun_maskActions
#check EffectiveEncoding.maskedCandidateDescriptorRun_generation
#print axioms EffectiveEncoding.maskedCandidateDescriptorRun_generation
#check EffectiveEncoding.maskedCandidateDescriptorRun_word
#print axioms EffectiveEncoding.maskedCandidateDescriptorRun_word
#check EffectiveEncoding.maskedCandidateDescriptorRun_maskActions
#print axioms EffectiveEncoding.maskedCandidateDescriptorRun_maskActions
#check EffectiveEncoding.maskedCandidateDescriptorRun_accountedActions
#print axioms EffectiveEncoding.maskedCandidateDescriptorRun_accountedActions
#check EffectiveEncoding.maskedCandidateDescriptorRun_accountedActions_polynomial
#print axioms EffectiveEncoding.maskedCandidateDescriptorRun_accountedActions_polynomial
#check EffectiveEncoding.maskedSerializedRun_execution
#print axioms EffectiveEncoding.maskedSerializedRun_execution
#check EffectiveEncoding.maskedSerializedRun_suffix_roundtrip
#print axioms EffectiveEncoding.maskedSerializedRun_suffix_roundtrip
#check EffectiveEncoding.maskedSerializedRun_decoded_word
#print axioms EffectiveEncoding.maskedSerializedRun_decoded_word
#check EffectiveEncoding.maskedSerializedRun_maskActions
#print axioms EffectiveEncoding.maskedSerializedRun_maskActions
#check EffectiveEncoding.maskedGeneration_uniform
#print axioms EffectiveEncoding.maskedGeneration_uniform
#check EffectiveEncoding.maskedSerializedRun_accountedPrimitiveActions_polynomial
#print axioms EffectiveEncoding.maskedSerializedRun_accountedPrimitiveActions_polynomial
#check EffectiveEncoding.maskedSerializedRun_fidelity
#print axioms EffectiveEncoding.maskedSerializedRun_fidelity
#check EffectiveEncoding.BinaryMaskPlanResult
#print axioms EffectiveEncoding.BinaryMaskPlanResult
#check EffectiveEncoding.binaryMaskPlanProgram
#print axioms EffectiveEncoding.binaryMaskPlanProgram
#check EffectiveEncoding.BinaryMaskPlanResult.copyActions
#print axioms EffectiveEncoding.BinaryMaskPlanResult.copyActions
#check EffectiveEncoding.BinaryMaskPlanResult.actions
#print axioms EffectiveEncoding.BinaryMaskPlanResult.actions
#check EffectiveEncoding.BinaryMaskRecord
#print axioms EffectiveEncoding.BinaryMaskRecord
#check EffectiveEncoding.MaskedCandidateResult
#print axioms EffectiveEncoding.MaskedCandidateResult
#check EffectiveEncoding.maskedCandidateOccupationRun
#print axioms EffectiveEncoding.maskedCandidateOccupationRun
#check EffectiveEncoding.MaskedCandidateResult.maskActions
#print axioms EffectiveEncoding.MaskedCandidateResult.maskActions
#check EffectiveEncoding.maskedCandidateStageRun
#print axioms EffectiveEncoding.maskedCandidateStageRun
#check EffectiveEncoding.maskedCandidateCompressionRun
#print axioms EffectiveEncoding.maskedCandidateCompressionRun
#check EffectiveEncoding.maskedCandidateDescriptorRun
#print axioms EffectiveEncoding.maskedCandidateDescriptorRun
#check EffectiveEncoding.MaskedCandidateResult.accountedActions
#print axioms EffectiveEncoding.MaskedCandidateResult.accountedActions
#check EffectiveEncoding.MaskedSerializedResult
#print axioms EffectiveEncoding.MaskedSerializedResult
#check EffectiveEncoding.maskedSerializedRun
#print axioms EffectiveEncoding.maskedSerializedRun
#check EffectiveEncoding.MaskedSerializedResult.decoded
#print axioms EffectiveEncoding.MaskedSerializedResult.decoded
#check EffectiveEncoding.MaskedSerializedResult.maskActions
#print axioms EffectiveEncoding.MaskedSerializedResult.maskActions
#check EffectiveEncoding.MaskedSerializedResult.accountedPrimitiveActions
#print axioms EffectiveEncoding.MaskedSerializedResult.accountedPrimitiveActions
#check EffectiveEncoding.maskedSerializedPolynomialConstant
#print axioms EffectiveEncoding.maskedSerializedPolynomialConstant
