import EffectiveEncoding.CandidateDescriptorGeneration

open Lean Elab Command
namespace EffectiveEncodingCandidateDescriptorVerification

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

end EffectiveEncodingCandidateDescriptorVerification

run_cmd (EffectiveEncodingCandidateDescriptorVerification.checkKinds [
  ``EffectiveEncoding.candidateNativeBranchEndpoint_point,
  ``EffectiveEncoding.candidateNativeNextEndpoint_point,
  ``EffectiveEncoding.candidateNativePivotEndpoint_point,
  ``EffectiveEncoding.candidateRankRecordsActions_append,
  ``EffectiveEncoding.candidateNativeBranchEndpoint_actions,
  ``EffectiveEncoding.candidateNativeNextEndpoint_actions,
  ``EffectiveEncoding.candidateNativePivotEndpoint_actions,
  ``EffectiveEncoding.candidateNativeTableProgram_counts,
  ``EffectiveEncoding.candidateNativeTableProgram_items,
  ``EffectiveEncoding.candidateNativeTableProgram_length,
  ``EffectiveEncoding.candidateEndpointMassActions,
  ``EffectiveEncoding.candidateIndexedRun_word,
  ``EffectiveEncoding.candidateIndexedRun_actions,
  ``EffectiveEncoding.candidateNativeBranchRun_word,
  ``EffectiveEncoding.candidateNativeBranchRun_actions,
  ``EffectiveEncoding.candidateAlignmentRun_word,
  ``EffectiveEncoding.candidateAlignmentRun_actions,
  ``EffectiveEncoding.candidateBranchTableRun_word,
  ``EffectiveEncoding.candidateBranchTableRun_actions,
  ``EffectiveEncoding.candidateOccupationRun_word,
  ``EffectiveEncoding.candidateOccupationRun_actions,
  ``EffectiveEncoding.candidateStageRun_word,
  ``EffectiveEncoding.candidateCompressionRun_word,
  ``EffectiveEncoding.candidateCompressionRun_actions,
  ``EffectiveEncoding.candidateDescriptorRun_word,
  ``EffectiveEncoding.candidateDescriptorRun_extractionCode,
  ``EffectiveEncoding.candidateDescriptorRun_actions
] [
  ``EffectiveEncoding.CandidateRankRecord,
  ``EffectiveEncoding.CandidateRankEndpoint,
  ``EffectiveEncoding.candidateNativeBranchEndpoint,
  ``EffectiveEncoding.candidateNativeNextEndpoint,
  ``EffectiveEncoding.candidateNativePivotEndpoint,
  ``EffectiveEncoding.candidateRankRecordsActions,
  ``EffectiveEncoding.CandidateRankEndpoint.actions,
  ``EffectiveEncoding.CandidateNativeTableResult,
  ``EffectiveEncoding.candidateNativeTableProgram,
  ``EffectiveEncoding.CandidateWordRun,
  ``EffectiveEncoding.CandidateWordRun.actions,
  ``EffectiveEncoding.candidateIndexedRun,
  ``EffectiveEncoding.candidateNativeBranchRun,
  ``EffectiveEncoding.candidateAlignmentRun,
  ``EffectiveEncoding.candidateBranchTableRun,
  ``EffectiveEncoding.CandidateDescriptorResult,
  ``EffectiveEncoding.CandidateDescriptorResult.actions,
  ``EffectiveEncoding.candidateOccupationRun,
  ``EffectiveEncoding.candidateStageRun,
  ``EffectiveEncoding.candidateCompressionRun,
  ``EffectiveEncoding.candidateDescriptorRun
])

#check EffectiveEncoding.candidateNativeBranchEndpoint_point
#print axioms EffectiveEncoding.candidateNativeBranchEndpoint_point
#check EffectiveEncoding.candidateNativeNextEndpoint_point
#print axioms EffectiveEncoding.candidateNativeNextEndpoint_point
#check EffectiveEncoding.candidateNativePivotEndpoint_point
#print axioms EffectiveEncoding.candidateNativePivotEndpoint_point
#check EffectiveEncoding.candidateRankRecordsActions_append
#print axioms EffectiveEncoding.candidateRankRecordsActions_append
#check EffectiveEncoding.candidateNativeBranchEndpoint_actions
#print axioms EffectiveEncoding.candidateNativeBranchEndpoint_actions
#check EffectiveEncoding.candidateNativeNextEndpoint_actions
#print axioms EffectiveEncoding.candidateNativeNextEndpoint_actions
#check EffectiveEncoding.candidateNativePivotEndpoint_actions
#print axioms EffectiveEncoding.candidateNativePivotEndpoint_actions
#check EffectiveEncoding.candidateNativeTableProgram_counts
#print axioms EffectiveEncoding.candidateNativeTableProgram_counts
#check EffectiveEncoding.candidateNativeTableProgram_items
#print axioms EffectiveEncoding.candidateNativeTableProgram_items
#check EffectiveEncoding.candidateNativeTableProgram_length
#print axioms EffectiveEncoding.candidateNativeTableProgram_length
#check EffectiveEncoding.candidateEndpointMassActions
#print axioms EffectiveEncoding.candidateEndpointMassActions
#check EffectiveEncoding.candidateIndexedRun_word
#print axioms EffectiveEncoding.candidateIndexedRun_word
#check EffectiveEncoding.candidateIndexedRun_actions
#print axioms EffectiveEncoding.candidateIndexedRun_actions
#check EffectiveEncoding.candidateNativeBranchRun_word
#print axioms EffectiveEncoding.candidateNativeBranchRun_word
#check EffectiveEncoding.candidateNativeBranchRun_actions
#print axioms EffectiveEncoding.candidateNativeBranchRun_actions
#check EffectiveEncoding.candidateAlignmentRun_word
#print axioms EffectiveEncoding.candidateAlignmentRun_word
#check EffectiveEncoding.candidateAlignmentRun_actions
#print axioms EffectiveEncoding.candidateAlignmentRun_actions
#check EffectiveEncoding.candidateBranchTableRun_word
#print axioms EffectiveEncoding.candidateBranchTableRun_word
#check EffectiveEncoding.candidateBranchTableRun_actions
#print axioms EffectiveEncoding.candidateBranchTableRun_actions
#check EffectiveEncoding.candidateOccupationRun_word
#print axioms EffectiveEncoding.candidateOccupationRun_word
#check EffectiveEncoding.candidateOccupationRun_actions
#print axioms EffectiveEncoding.candidateOccupationRun_actions
#check EffectiveEncoding.candidateStageRun_word
#print axioms EffectiveEncoding.candidateStageRun_word
#check EffectiveEncoding.candidateCompressionRun_word
#print axioms EffectiveEncoding.candidateCompressionRun_word
#check EffectiveEncoding.candidateCompressionRun_actions
#print axioms EffectiveEncoding.candidateCompressionRun_actions
#check EffectiveEncoding.candidateDescriptorRun_word
#print axioms EffectiveEncoding.candidateDescriptorRun_word
#check EffectiveEncoding.candidateDescriptorRun_extractionCode
#print axioms EffectiveEncoding.candidateDescriptorRun_extractionCode
#check EffectiveEncoding.candidateDescriptorRun_actions
#print axioms EffectiveEncoding.candidateDescriptorRun_actions
#check EffectiveEncoding.CandidateRankRecord
#print axioms EffectiveEncoding.CandidateRankRecord
#check EffectiveEncoding.CandidateRankEndpoint
#print axioms EffectiveEncoding.CandidateRankEndpoint
#check EffectiveEncoding.candidateNativeBranchEndpoint
#print axioms EffectiveEncoding.candidateNativeBranchEndpoint
#check EffectiveEncoding.candidateNativeNextEndpoint
#print axioms EffectiveEncoding.candidateNativeNextEndpoint
#check EffectiveEncoding.candidateNativePivotEndpoint
#print axioms EffectiveEncoding.candidateNativePivotEndpoint
#check EffectiveEncoding.candidateRankRecordsActions
#print axioms EffectiveEncoding.candidateRankRecordsActions
#check EffectiveEncoding.CandidateRankEndpoint.actions
#print axioms EffectiveEncoding.CandidateRankEndpoint.actions
#check EffectiveEncoding.CandidateNativeTableResult
#print axioms EffectiveEncoding.CandidateNativeTableResult
#check EffectiveEncoding.candidateNativeTableProgram
#print axioms EffectiveEncoding.candidateNativeTableProgram
#check EffectiveEncoding.CandidateWordRun
#print axioms EffectiveEncoding.CandidateWordRun
#check EffectiveEncoding.CandidateWordRun.actions
#print axioms EffectiveEncoding.CandidateWordRun.actions
#check EffectiveEncoding.candidateIndexedRun
#print axioms EffectiveEncoding.candidateIndexedRun
#check EffectiveEncoding.candidateNativeBranchRun
#print axioms EffectiveEncoding.candidateNativeBranchRun
#check EffectiveEncoding.candidateAlignmentRun
#print axioms EffectiveEncoding.candidateAlignmentRun
#check EffectiveEncoding.candidateBranchTableRun
#print axioms EffectiveEncoding.candidateBranchTableRun
#check EffectiveEncoding.CandidateDescriptorResult
#print axioms EffectiveEncoding.CandidateDescriptorResult
#check EffectiveEncoding.CandidateDescriptorResult.actions
#print axioms EffectiveEncoding.CandidateDescriptorResult.actions
#check EffectiveEncoding.candidateOccupationRun
#print axioms EffectiveEncoding.candidateOccupationRun
#check EffectiveEncoding.candidateStageRun
#print axioms EffectiveEncoding.candidateStageRun
#check EffectiveEncoding.candidateCompressionRun
#print axioms EffectiveEncoding.candidateCompressionRun
#check EffectiveEncoding.candidateDescriptorRun
#print axioms EffectiveEncoding.candidateDescriptorRun
