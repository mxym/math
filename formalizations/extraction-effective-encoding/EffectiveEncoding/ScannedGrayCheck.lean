import EffectiveEncoding.ScannedGraySerializedRun
import EffectiveEncoding.ScannedGrayEvaluation

open Lean Elab Command
namespace EffectiveEncodingScannedGrayVerification

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

end EffectiveEncodingScannedGrayVerification

run_cmd (EffectiveEncodingScannedGrayVerification.checkKinds [
  ``EffectiveEncoding.booleanGrayScanProgram_actions,
  ``EffectiveEncoding.booleanGrayScanProgram_first,
  ``EffectiveEncoding.booleanGrayScanProgram_first_mem,
  ``EffectiveEncoding.booleanGrayScanProgram_others,
  ``EffectiveEncoding.booleanGrayScanProgram_none,
  ``EffectiveEncoding.packedListProjectionProgram_bits,
  ``EffectiveEncoding.packedGrayScanProgram_first,
  ``EffectiveEncoding.packedGrayScanProgram_actions,
  ``EffectiveEncoding.packedGrayDifferences_sorted,
  ``EffectiveEncoding.packedGrayScanProgram_none,
  ``EffectiveEncoding.packedGrayScanProgram_first_eq,
  ``EffectiveEncoding.finRange_erase_otherWires,
  ``EffectiveEncoding.packedGrayScanProgram_others_eq,
  ``EffectiveEncoding.scannedPreparedSwapProgram_word,
  ``EffectiveEncoding.scannedPreparedRotationProgram_word,
  ``EffectiveEncoding.scannedPreparedRotationProgram_equal_word,
  ``EffectiveEncoding.scannedPreparedSwapProgram_actions,
  ``EffectiveEncoding.scannedPreparedRotationProgram_actions,
  ``EffectiveEncoding.scannedPreparedSwapProgram_forward_length,
  ``EffectiveEncoding.scannedPreparedRotationProgram_forward_length,
  ``EffectiveEncoding.scannedPreparedSwapProgram_actions_word,
  ``EffectiveEncoding.scannedPreparedRotationProgram_actions_word,
  ``EffectiveEncoding.scannedEntryCompileProgram_word,
  ``EffectiveEncoding.scannedEntryCompileProgram_grayCount,
  ``EffectiveEncoding.grayListIndexedCandidateRun_common,
  ``EffectiveEncoding.grayListIndexedCandidateRun_grayCount,
  ``EffectiveEncoding.scannedEntryCompileProgram_actions,
  ``EffectiveEncoding.grayListIndexedCandidateRun_actions,
  ``EffectiveEncoding.grayStoredLettersBranchRun_common,
  ``EffectiveEncoding.typedOccupationLetters_length,
  ``EffectiveEncoding.grayStoredLettersBranchRun_actions,
  ``EffectiveEncoding.grayStoredLettersBranchTableRun_common,
  ``EffectiveEncoding.grayStoredLettersBranchTableRun_actions,
  ``EffectiveEncoding.grayStoredLettersAlignmentRun_common,
  ``EffectiveEncoding.grayStoredLettersAlignmentRun_actions,
  ``EffectiveEncoding.scannedGrayOccupationRun_common,
  ``EffectiveEncoding.scannedGrayOccupationRun_grayActions,
  ``EffectiveEncoding.scannedGrayStageRun_common,
  ``EffectiveEncoding.scannedGrayCompressionRun_common,
  ``EffectiveEncoding.scannedGrayCompressionRun_grayActions,
  ``EffectiveEncoding.scannedGrayDescriptorRun_common,
  ``EffectiveEncoding.scannedGrayDescriptorRun_word,
  ``EffectiveEncoding.scannedGrayDescriptorRun_grayActions,
  ``EffectiveEncoding.scannedGraySerializedRun_common,
  ``EffectiveEncoding.scannedGraySerializedRun_suffix_roundtrip,
  ``EffectiveEncoding.scannedGraySerializedRun_decoded_word,
  ``EffectiveEncoding.scannedGraySerializedRun_grayActions,
  ``EffectiveEncoding.scannedGrayGeneration_uniform,
  ``EffectiveEncoding.scannedGraySerializedRun_accountedPrimitiveActions_polynomial,
  ``EffectiveEncoding.scannedGraySerializedRun_fidelity
] [
  ``EffectiveEncoding.GrayScanTrace,
  ``EffectiveEncoding.BooleanGrayScanResult,
  ``EffectiveEncoding.booleanGrayScanProgram,
  ``EffectiveEncoding.GrayScanTrace.actions,
  ``EffectiveEncoding.PackedListProjectionTrace,
  ``EffectiveEncoding.PackedListProjectionResult,
  ``EffectiveEncoding.packedListProjectionProgram,
  ``EffectiveEncoding.PackedListProjectionTrace.actions,
  ``EffectiveEncoding.PackedGrayScanResult,
  ``EffectiveEncoding.packedGrayScanProgram,
  ``EffectiveEncoding.PackedGrayScanResult.actions,
  ``EffectiveEncoding.ScannedGrayCompileResult,
  ``EffectiveEncoding.scannedPreparedSwapProgram,
  ``EffectiveEncoding.scannedPreparedRotationProgram,
  ``EffectiveEncoding.ScannedGrayCompileResult.actions,
  ``EffectiveEncoding.ScannedEntryCompileResult,
  ``EffectiveEncoding.scannedEntryCompileProgram,
  ``EffectiveEncoding.ScannedCandidateWordRun,
  ``EffectiveEncoding.grayListIndexedCandidateRun,
  ``EffectiveEncoding.ScannedEntryCompileResult.actions,
  ``EffectiveEncoding.ScannedCandidateWordRun.actions,
  ``EffectiveEncoding.grayStoredLettersBranchRun,
  ``EffectiveEncoding.grayStoredLettersBranchTableRun,
  ``EffectiveEncoding.grayStoredLettersAlignmentRun,
  ``EffectiveEncoding.ScannedGrayRecord,
  ``EffectiveEncoding.ScannedGrayCandidateResult,
  ``EffectiveEncoding.ScannedGrayCandidateResult.word,
  ``EffectiveEncoding.scannedGrayOccupationRun,
  ``EffectiveEncoding.ScannedGrayCandidateResult.grayActions,
  ``EffectiveEncoding.scannedGrayStageRun,
  ``EffectiveEncoding.scannedGrayCompressionRun,
  ``EffectiveEncoding.scannedGrayDescriptorRun,
  ``EffectiveEncoding.ScannedGraySerializedResult,
  ``EffectiveEncoding.scannedGraySerializedRun,
  ``EffectiveEncoding.ScannedGraySerializedResult.decoded,
  ``EffectiveEncoding.ScannedGraySerializedResult.grayActions,
  ``EffectiveEncoding.ScannedGraySerializedResult.accountedPrimitiveActions,
  ``EffectiveEncoding.scannedGraySerializedPolynomialConstant
])

#check EffectiveEncoding.booleanGrayScanProgram_actions
#print axioms EffectiveEncoding.booleanGrayScanProgram_actions
#check EffectiveEncoding.booleanGrayScanProgram_first
#print axioms EffectiveEncoding.booleanGrayScanProgram_first
#check EffectiveEncoding.booleanGrayScanProgram_first_mem
#print axioms EffectiveEncoding.booleanGrayScanProgram_first_mem
#check EffectiveEncoding.booleanGrayScanProgram_others
#print axioms EffectiveEncoding.booleanGrayScanProgram_others
#check EffectiveEncoding.booleanGrayScanProgram_none
#print axioms EffectiveEncoding.booleanGrayScanProgram_none
#check EffectiveEncoding.packedListProjectionProgram_bits
#print axioms EffectiveEncoding.packedListProjectionProgram_bits
#check EffectiveEncoding.packedGrayScanProgram_first
#print axioms EffectiveEncoding.packedGrayScanProgram_first
#check EffectiveEncoding.packedGrayScanProgram_actions
#print axioms EffectiveEncoding.packedGrayScanProgram_actions
#check EffectiveEncoding.packedGrayDifferences_sorted
#print axioms EffectiveEncoding.packedGrayDifferences_sorted
#check EffectiveEncoding.packedGrayScanProgram_none
#print axioms EffectiveEncoding.packedGrayScanProgram_none
#check EffectiveEncoding.packedGrayScanProgram_first_eq
#print axioms EffectiveEncoding.packedGrayScanProgram_first_eq
#check EffectiveEncoding.finRange_erase_otherWires
#print axioms EffectiveEncoding.finRange_erase_otherWires
#check EffectiveEncoding.packedGrayScanProgram_others_eq
#print axioms EffectiveEncoding.packedGrayScanProgram_others_eq
#check EffectiveEncoding.scannedPreparedSwapProgram_word
#print axioms EffectiveEncoding.scannedPreparedSwapProgram_word
#check EffectiveEncoding.scannedPreparedRotationProgram_word
#print axioms EffectiveEncoding.scannedPreparedRotationProgram_word
#check EffectiveEncoding.scannedPreparedRotationProgram_equal_word
#print axioms EffectiveEncoding.scannedPreparedRotationProgram_equal_word
#check EffectiveEncoding.scannedPreparedSwapProgram_actions
#print axioms EffectiveEncoding.scannedPreparedSwapProgram_actions
#check EffectiveEncoding.scannedPreparedRotationProgram_actions
#print axioms EffectiveEncoding.scannedPreparedRotationProgram_actions
#check EffectiveEncoding.scannedPreparedSwapProgram_forward_length
#print axioms EffectiveEncoding.scannedPreparedSwapProgram_forward_length
#check EffectiveEncoding.scannedPreparedRotationProgram_forward_length
#print axioms EffectiveEncoding.scannedPreparedRotationProgram_forward_length
#check EffectiveEncoding.scannedPreparedSwapProgram_actions_word
#print axioms EffectiveEncoding.scannedPreparedSwapProgram_actions_word
#check EffectiveEncoding.scannedPreparedRotationProgram_actions_word
#print axioms EffectiveEncoding.scannedPreparedRotationProgram_actions_word
#check EffectiveEncoding.scannedEntryCompileProgram_word
#print axioms EffectiveEncoding.scannedEntryCompileProgram_word
#check EffectiveEncoding.scannedEntryCompileProgram_grayCount
#print axioms EffectiveEncoding.scannedEntryCompileProgram_grayCount
#check EffectiveEncoding.grayListIndexedCandidateRun_common
#print axioms EffectiveEncoding.grayListIndexedCandidateRun_common
#check EffectiveEncoding.grayListIndexedCandidateRun_grayCount
#print axioms EffectiveEncoding.grayListIndexedCandidateRun_grayCount
#check EffectiveEncoding.scannedEntryCompileProgram_actions
#print axioms EffectiveEncoding.scannedEntryCompileProgram_actions
#check EffectiveEncoding.grayListIndexedCandidateRun_actions
#print axioms EffectiveEncoding.grayListIndexedCandidateRun_actions
#check EffectiveEncoding.grayStoredLettersBranchRun_common
#print axioms EffectiveEncoding.grayStoredLettersBranchRun_common
#check EffectiveEncoding.typedOccupationLetters_length
#print axioms EffectiveEncoding.typedOccupationLetters_length
#check EffectiveEncoding.grayStoredLettersBranchRun_actions
#print axioms EffectiveEncoding.grayStoredLettersBranchRun_actions
#check EffectiveEncoding.grayStoredLettersBranchTableRun_common
#print axioms EffectiveEncoding.grayStoredLettersBranchTableRun_common
#check EffectiveEncoding.grayStoredLettersBranchTableRun_actions
#print axioms EffectiveEncoding.grayStoredLettersBranchTableRun_actions
#check EffectiveEncoding.grayStoredLettersAlignmentRun_common
#print axioms EffectiveEncoding.grayStoredLettersAlignmentRun_common
#check EffectiveEncoding.grayStoredLettersAlignmentRun_actions
#print axioms EffectiveEncoding.grayStoredLettersAlignmentRun_actions
#check EffectiveEncoding.scannedGrayOccupationRun_common
#print axioms EffectiveEncoding.scannedGrayOccupationRun_common
#check EffectiveEncoding.scannedGrayOccupationRun_grayActions
#print axioms EffectiveEncoding.scannedGrayOccupationRun_grayActions
#check EffectiveEncoding.scannedGrayStageRun_common
#print axioms EffectiveEncoding.scannedGrayStageRun_common
#check EffectiveEncoding.scannedGrayCompressionRun_common
#print axioms EffectiveEncoding.scannedGrayCompressionRun_common
#check EffectiveEncoding.scannedGrayCompressionRun_grayActions
#print axioms EffectiveEncoding.scannedGrayCompressionRun_grayActions
#check EffectiveEncoding.scannedGrayDescriptorRun_common
#print axioms EffectiveEncoding.scannedGrayDescriptorRun_common
#check EffectiveEncoding.scannedGrayDescriptorRun_word
#print axioms EffectiveEncoding.scannedGrayDescriptorRun_word
#check EffectiveEncoding.scannedGrayDescriptorRun_grayActions
#print axioms EffectiveEncoding.scannedGrayDescriptorRun_grayActions
#check EffectiveEncoding.scannedGraySerializedRun_common
#print axioms EffectiveEncoding.scannedGraySerializedRun_common
#check EffectiveEncoding.scannedGraySerializedRun_suffix_roundtrip
#print axioms EffectiveEncoding.scannedGraySerializedRun_suffix_roundtrip
#check EffectiveEncoding.scannedGraySerializedRun_decoded_word
#print axioms EffectiveEncoding.scannedGraySerializedRun_decoded_word
#check EffectiveEncoding.scannedGraySerializedRun_grayActions
#print axioms EffectiveEncoding.scannedGraySerializedRun_grayActions
#check EffectiveEncoding.scannedGrayGeneration_uniform
#print axioms EffectiveEncoding.scannedGrayGeneration_uniform
#check EffectiveEncoding.scannedGraySerializedRun_accountedPrimitiveActions_polynomial
#print axioms EffectiveEncoding.scannedGraySerializedRun_accountedPrimitiveActions_polynomial
#check EffectiveEncoding.scannedGraySerializedRun_fidelity
#print axioms EffectiveEncoding.scannedGraySerializedRun_fidelity
#check EffectiveEncoding.GrayScanTrace
#print axioms EffectiveEncoding.GrayScanTrace
#check EffectiveEncoding.BooleanGrayScanResult
#print axioms EffectiveEncoding.BooleanGrayScanResult
#check EffectiveEncoding.booleanGrayScanProgram
#print axioms EffectiveEncoding.booleanGrayScanProgram
#check EffectiveEncoding.GrayScanTrace.actions
#print axioms EffectiveEncoding.GrayScanTrace.actions
#check EffectiveEncoding.PackedListProjectionTrace
#print axioms EffectiveEncoding.PackedListProjectionTrace
#check EffectiveEncoding.PackedListProjectionResult
#print axioms EffectiveEncoding.PackedListProjectionResult
#check EffectiveEncoding.packedListProjectionProgram
#print axioms EffectiveEncoding.packedListProjectionProgram
#check EffectiveEncoding.PackedListProjectionTrace.actions
#print axioms EffectiveEncoding.PackedListProjectionTrace.actions
#check EffectiveEncoding.PackedGrayScanResult
#print axioms EffectiveEncoding.PackedGrayScanResult
#check EffectiveEncoding.packedGrayScanProgram
#print axioms EffectiveEncoding.packedGrayScanProgram
#check EffectiveEncoding.PackedGrayScanResult.actions
#print axioms EffectiveEncoding.PackedGrayScanResult.actions
#check EffectiveEncoding.ScannedGrayCompileResult
#print axioms EffectiveEncoding.ScannedGrayCompileResult
#check EffectiveEncoding.scannedPreparedSwapProgram
#print axioms EffectiveEncoding.scannedPreparedSwapProgram
#check EffectiveEncoding.scannedPreparedRotationProgram
#print axioms EffectiveEncoding.scannedPreparedRotationProgram
#check EffectiveEncoding.ScannedGrayCompileResult.actions
#print axioms EffectiveEncoding.ScannedGrayCompileResult.actions
#check EffectiveEncoding.ScannedEntryCompileResult
#print axioms EffectiveEncoding.ScannedEntryCompileResult
#check EffectiveEncoding.scannedEntryCompileProgram
#print axioms EffectiveEncoding.scannedEntryCompileProgram
#check EffectiveEncoding.ScannedCandidateWordRun
#print axioms EffectiveEncoding.ScannedCandidateWordRun
#check EffectiveEncoding.grayListIndexedCandidateRun
#print axioms EffectiveEncoding.grayListIndexedCandidateRun
#check EffectiveEncoding.ScannedEntryCompileResult.actions
#print axioms EffectiveEncoding.ScannedEntryCompileResult.actions
#check EffectiveEncoding.ScannedCandidateWordRun.actions
#print axioms EffectiveEncoding.ScannedCandidateWordRun.actions
#check EffectiveEncoding.grayStoredLettersBranchRun
#print axioms EffectiveEncoding.grayStoredLettersBranchRun
#check EffectiveEncoding.grayStoredLettersBranchTableRun
#print axioms EffectiveEncoding.grayStoredLettersBranchTableRun
#check EffectiveEncoding.grayStoredLettersAlignmentRun
#print axioms EffectiveEncoding.grayStoredLettersAlignmentRun
#check EffectiveEncoding.ScannedGrayRecord
#print axioms EffectiveEncoding.ScannedGrayRecord
#check EffectiveEncoding.ScannedGrayCandidateResult
#print axioms EffectiveEncoding.ScannedGrayCandidateResult
#check EffectiveEncoding.ScannedGrayCandidateResult.word
#print axioms EffectiveEncoding.ScannedGrayCandidateResult.word
#check EffectiveEncoding.scannedGrayOccupationRun
#print axioms EffectiveEncoding.scannedGrayOccupationRun
#check EffectiveEncoding.ScannedGrayCandidateResult.grayActions
#print axioms EffectiveEncoding.ScannedGrayCandidateResult.grayActions
#check EffectiveEncoding.scannedGrayStageRun
#print axioms EffectiveEncoding.scannedGrayStageRun
#check EffectiveEncoding.scannedGrayCompressionRun
#print axioms EffectiveEncoding.scannedGrayCompressionRun
#check EffectiveEncoding.scannedGrayDescriptorRun
#print axioms EffectiveEncoding.scannedGrayDescriptorRun
#check EffectiveEncoding.ScannedGraySerializedResult
#print axioms EffectiveEncoding.ScannedGraySerializedResult
#check EffectiveEncoding.scannedGraySerializedRun
#print axioms EffectiveEncoding.scannedGraySerializedRun
#check EffectiveEncoding.ScannedGraySerializedResult.decoded
#print axioms EffectiveEncoding.ScannedGraySerializedResult.decoded
#check EffectiveEncoding.ScannedGraySerializedResult.grayActions
#print axioms EffectiveEncoding.ScannedGraySerializedResult.grayActions
#check EffectiveEncoding.ScannedGraySerializedResult.accountedPrimitiveActions
#print axioms EffectiveEncoding.ScannedGraySerializedResult.accountedPrimitiveActions
#check EffectiveEncoding.scannedGraySerializedPolynomialConstant
#print axioms EffectiveEncoding.scannedGraySerializedPolynomialConstant
