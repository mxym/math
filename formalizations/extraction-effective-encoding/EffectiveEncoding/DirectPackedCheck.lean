import EffectiveEncoding.DirectPackedExtraction

open Lean Elab Command
namespace EffectiveEncodingDirectPackedVerification

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

end EffectiveEncodingDirectPackedVerification

run_cmd (EffectiveEncodingDirectPackedVerification.checkKinds [
  ``EffectiveEncoding.packBits_eq_iff,
  ``EffectiveEncoding.packedEntryProgram_indexed,
  ``EffectiveEncoding.packedIndexedRun_word,
  ``EffectiveEncoding.packedIndexedRun_requests,
  ``EffectiveEncoding.packedBranchRun_word,
  ``EffectiveEncoding.packedBranchRun_requests,
  ``EffectiveEncoding.requestedAlignmentRun_result,
  ``EffectiveEncoding.requestedAlignmentRun_requests,
  ``EffectiveEncoding.packedBranchTableRun_word,
  ``EffectiveEncoding.packedBranchTableRun_requests,
  ``EffectiveEncoding.directPackedOccupationRun_word,
  ``EffectiveEncoding.directPackedOccupationRun_requests,
  ``EffectiveEncoding.directPackedStageRun_word,
  ``EffectiveEncoding.directPackedCompressionCode_eq,
  ``EffectiveEncoding.directPackedDescriptorCode_eq,
  ``EffectiveEncoding.directPackedExtractionCode_eq,
  ``EffectiveEncoding.directPackedExtractionCode_fidelity,
  ``EffectiveEncoding.extractionBranchEmbeddingRequests_bound
] [
  ``EffectiveEncoding.packedEntryProgram,
  ``EffectiveEncoding.packedIndexedEntries,
  ``EffectiveEncoding.PackedIndexedRun,
  ``EffectiveEncoding.packedIndexedRun,
  ``EffectiveEncoding.packedBranchRun,
  ``EffectiveEncoding.RequestedAlignmentRun,
  ``EffectiveEncoding.requestedAlignmentRun,
  ``EffectiveEncoding.packedBranchTableRun,
  ``EffectiveEncoding.directPackedOccupationRun,
  ``EffectiveEncoding.directPackedStageRun,
  ``EffectiveEncoding.directPackedCompressionCode,
  ``EffectiveEncoding.directPackedDescriptorCode,
  ``EffectiveEncoding.directPackedExtractionCode,
  ``EffectiveEncoding.extractionBranchEmbeddingRequests
])

#check EffectiveEncoding.packBits_eq_iff
#print axioms EffectiveEncoding.packBits_eq_iff
#check EffectiveEncoding.packedEntryProgram_indexed
#print axioms EffectiveEncoding.packedEntryProgram_indexed
#check EffectiveEncoding.packedIndexedRun_word
#print axioms EffectiveEncoding.packedIndexedRun_word
#check EffectiveEncoding.packedIndexedRun_requests
#print axioms EffectiveEncoding.packedIndexedRun_requests
#check EffectiveEncoding.packedBranchRun_word
#print axioms EffectiveEncoding.packedBranchRun_word
#check EffectiveEncoding.packedBranchRun_requests
#print axioms EffectiveEncoding.packedBranchRun_requests
#check EffectiveEncoding.requestedAlignmentRun_result
#print axioms EffectiveEncoding.requestedAlignmentRun_result
#check EffectiveEncoding.requestedAlignmentRun_requests
#print axioms EffectiveEncoding.requestedAlignmentRun_requests
#check EffectiveEncoding.packedBranchTableRun_word
#print axioms EffectiveEncoding.packedBranchTableRun_word
#check EffectiveEncoding.packedBranchTableRun_requests
#print axioms EffectiveEncoding.packedBranchTableRun_requests
#check EffectiveEncoding.directPackedOccupationRun_word
#print axioms EffectiveEncoding.directPackedOccupationRun_word
#check EffectiveEncoding.directPackedOccupationRun_requests
#print axioms EffectiveEncoding.directPackedOccupationRun_requests
#check EffectiveEncoding.directPackedStageRun_word
#print axioms EffectiveEncoding.directPackedStageRun_word
#check EffectiveEncoding.directPackedCompressionCode_eq
#print axioms EffectiveEncoding.directPackedCompressionCode_eq
#check EffectiveEncoding.directPackedDescriptorCode_eq
#print axioms EffectiveEncoding.directPackedDescriptorCode_eq
#check EffectiveEncoding.directPackedExtractionCode_eq
#print axioms EffectiveEncoding.directPackedExtractionCode_eq
#check EffectiveEncoding.directPackedExtractionCode_fidelity
#print axioms EffectiveEncoding.directPackedExtractionCode_fidelity
#check EffectiveEncoding.extractionBranchEmbeddingRequests_bound
#print axioms EffectiveEncoding.extractionBranchEmbeddingRequests_bound
#check EffectiveEncoding.packedEntryProgram
#print axioms EffectiveEncoding.packedEntryProgram
#check EffectiveEncoding.packedIndexedEntries
#print axioms EffectiveEncoding.packedIndexedEntries
#check EffectiveEncoding.PackedIndexedRun
#print axioms EffectiveEncoding.PackedIndexedRun
#check EffectiveEncoding.packedIndexedRun
#print axioms EffectiveEncoding.packedIndexedRun
#check EffectiveEncoding.packedBranchRun
#print axioms EffectiveEncoding.packedBranchRun
#check EffectiveEncoding.RequestedAlignmentRun
#print axioms EffectiveEncoding.RequestedAlignmentRun
#check EffectiveEncoding.requestedAlignmentRun
#print axioms EffectiveEncoding.requestedAlignmentRun
#check EffectiveEncoding.packedBranchTableRun
#print axioms EffectiveEncoding.packedBranchTableRun
#check EffectiveEncoding.directPackedOccupationRun
#print axioms EffectiveEncoding.directPackedOccupationRun
#check EffectiveEncoding.directPackedStageRun
#print axioms EffectiveEncoding.directPackedStageRun
#check EffectiveEncoding.directPackedCompressionCode
#print axioms EffectiveEncoding.directPackedCompressionCode
#check EffectiveEncoding.directPackedDescriptorCode
#print axioms EffectiveEncoding.directPackedDescriptorCode
#check EffectiveEncoding.directPackedExtractionCode
#print axioms EffectiveEncoding.directPackedExtractionCode
#check EffectiveEncoding.extractionBranchEmbeddingRequests
#print axioms EffectiveEncoding.extractionBranchEmbeddingRequests
