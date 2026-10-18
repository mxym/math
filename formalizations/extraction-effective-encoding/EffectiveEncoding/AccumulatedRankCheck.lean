import EffectiveEncoding.AccumulatedRankExtraction

open Lean Elab Command
namespace EffectiveEncodingAccumulatedRankVerification

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

end EffectiveEncodingAccumulatedRankVerification

run_cmd (EffectiveEncodingAccumulatedRankVerification.checkKinds [
  ``EffectiveEncoding.encodedOccupationProgram_value,
  ``EffectiveEncoding.encodedOccupationProgram_work,
  ``EffectiveEncoding.encodedBranchEndpoint_value,
  ``EffectiveEncoding.encodedBranchEndpoint_work,
  ``EffectiveEncoding.encodedNextEndpoint_value,
  ``EffectiveEncoding.encodedNextEndpoint_work,
  ``EffectiveEncoding.endpointMassWork_bound,
  ``EffectiveEncoding.rankedIndexedRun_word,
  ``EffectiveEncoding.rankedIndexedRun_work,
  ``EffectiveEncoding.rankedBranchRun_word,
  ``EffectiveEncoding.rankedBranchRun_work,
  ``EffectiveEncoding.rankedAlignmentRun_result,
  ``EffectiveEncoding.rankedAlignmentRun_work,
  ``EffectiveEncoding.encodedPivotEndpoint_value,
  ``EffectiveEncoding.encodedPivotEndpoint_work,
  ``EffectiveEncoding.rankedBranchTableRun_word,
  ``EffectiveEncoding.rankedBranchTableRun_work,
  ``EffectiveEncoding.rankedOccupationRun_word,
  ``EffectiveEncoding.rankedOccupationRun_work,
  ``EffectiveEncoding.rankedStageRun_word,
  ``EffectiveEncoding.rankedCompressionRun_word,
  ``EffectiveEncoding.rankedCompressionRun_work,
  ``EffectiveEncoding.rankedDescriptorRun_word,
  ``EffectiveEncoding.rankedDescriptorRun_work,
  ``EffectiveEncoding.rankedExtractionRun_word,
  ``EffectiveEncoding.rankedExtractionRun_work,
  ``EffectiveEncoding.rankedExtractionRun_constructionSteps,
  ``EffectiveEncoding.rankedExtractionRun_predicateQueries,
  ``EffectiveEncoding.rankedExtractionRun_natEqualityQueries,
  ``EffectiveEncoding.rankedExtractionRun_fidelity
] [
  ``EffectiveEncoding.RankWork,
  ``EffectiveEncoding.rankWorkConstant,
  ``EffectiveEncoding.EncodedEndpoint,
  ``EffectiveEncoding.encodedOccupationProgram,
  ``EffectiveEncoding.encodedBranchEndpoint,
  ``EffectiveEncoding.encodedNextEndpoint,
  ``EffectiveEncoding.endpointMassWork,
  ``EffectiveEncoding.RankedBranchRun,
  ``EffectiveEncoding.rankedIndexedRun,
  ``EffectiveEncoding.rankedBranchRun,
  ``EffectiveEncoding.RankedAlignmentRun,
  ``EffectiveEncoding.rankedAlignmentRun,
  ``EffectiveEncoding.encodedPivotEndpoint,
  ``EffectiveEncoding.rankedBranchTableRun,
  ``EffectiveEncoding.rankedOccupationRun,
  ``EffectiveEncoding.rankedStageRun,
  ``EffectiveEncoding.rankedCompressionRun,
  ``EffectiveEncoding.rankedDescriptorRun,
  ``EffectiveEncoding.RankedLabelRun,
  ``EffectiveEncoding.rankedExtractionRun
])

#check EffectiveEncoding.encodedOccupationProgram_value
#print axioms EffectiveEncoding.encodedOccupationProgram_value
#check EffectiveEncoding.encodedOccupationProgram_work
#print axioms EffectiveEncoding.encodedOccupationProgram_work
#check EffectiveEncoding.encodedBranchEndpoint_value
#print axioms EffectiveEncoding.encodedBranchEndpoint_value
#check EffectiveEncoding.encodedBranchEndpoint_work
#print axioms EffectiveEncoding.encodedBranchEndpoint_work
#check EffectiveEncoding.encodedNextEndpoint_value
#print axioms EffectiveEncoding.encodedNextEndpoint_value
#check EffectiveEncoding.encodedNextEndpoint_work
#print axioms EffectiveEncoding.encodedNextEndpoint_work
#check EffectiveEncoding.endpointMassWork_bound
#print axioms EffectiveEncoding.endpointMassWork_bound
#check EffectiveEncoding.rankedIndexedRun_word
#print axioms EffectiveEncoding.rankedIndexedRun_word
#check EffectiveEncoding.rankedIndexedRun_work
#print axioms EffectiveEncoding.rankedIndexedRun_work
#check EffectiveEncoding.rankedBranchRun_word
#print axioms EffectiveEncoding.rankedBranchRun_word
#check EffectiveEncoding.rankedBranchRun_work
#print axioms EffectiveEncoding.rankedBranchRun_work
#check EffectiveEncoding.rankedAlignmentRun_result
#print axioms EffectiveEncoding.rankedAlignmentRun_result
#check EffectiveEncoding.rankedAlignmentRun_work
#print axioms EffectiveEncoding.rankedAlignmentRun_work
#check EffectiveEncoding.encodedPivotEndpoint_value
#print axioms EffectiveEncoding.encodedPivotEndpoint_value
#check EffectiveEncoding.encodedPivotEndpoint_work
#print axioms EffectiveEncoding.encodedPivotEndpoint_work
#check EffectiveEncoding.rankedBranchTableRun_word
#print axioms EffectiveEncoding.rankedBranchTableRun_word
#check EffectiveEncoding.rankedBranchTableRun_work
#print axioms EffectiveEncoding.rankedBranchTableRun_work
#check EffectiveEncoding.rankedOccupationRun_word
#print axioms EffectiveEncoding.rankedOccupationRun_word
#check EffectiveEncoding.rankedOccupationRun_work
#print axioms EffectiveEncoding.rankedOccupationRun_work
#check EffectiveEncoding.rankedStageRun_word
#print axioms EffectiveEncoding.rankedStageRun_word
#check EffectiveEncoding.rankedCompressionRun_word
#print axioms EffectiveEncoding.rankedCompressionRun_word
#check EffectiveEncoding.rankedCompressionRun_work
#print axioms EffectiveEncoding.rankedCompressionRun_work
#check EffectiveEncoding.rankedDescriptorRun_word
#print axioms EffectiveEncoding.rankedDescriptorRun_word
#check EffectiveEncoding.rankedDescriptorRun_work
#print axioms EffectiveEncoding.rankedDescriptorRun_work
#check EffectiveEncoding.rankedExtractionRun_word
#print axioms EffectiveEncoding.rankedExtractionRun_word
#check EffectiveEncoding.rankedExtractionRun_work
#print axioms EffectiveEncoding.rankedExtractionRun_work
#check EffectiveEncoding.rankedExtractionRun_constructionSteps
#print axioms EffectiveEncoding.rankedExtractionRun_constructionSteps
#check EffectiveEncoding.rankedExtractionRun_predicateQueries
#print axioms EffectiveEncoding.rankedExtractionRun_predicateQueries
#check EffectiveEncoding.rankedExtractionRun_natEqualityQueries
#print axioms EffectiveEncoding.rankedExtractionRun_natEqualityQueries
#check EffectiveEncoding.rankedExtractionRun_fidelity
#print axioms EffectiveEncoding.rankedExtractionRun_fidelity
#check EffectiveEncoding.RankWork
#print axioms EffectiveEncoding.RankWork
#check EffectiveEncoding.rankWorkConstant
#print axioms EffectiveEncoding.rankWorkConstant
#check EffectiveEncoding.EncodedEndpoint
#print axioms EffectiveEncoding.EncodedEndpoint
#check EffectiveEncoding.encodedOccupationProgram
#print axioms EffectiveEncoding.encodedOccupationProgram
#check EffectiveEncoding.encodedBranchEndpoint
#print axioms EffectiveEncoding.encodedBranchEndpoint
#check EffectiveEncoding.encodedNextEndpoint
#print axioms EffectiveEncoding.encodedNextEndpoint
#check EffectiveEncoding.endpointMassWork
#print axioms EffectiveEncoding.endpointMassWork
#check EffectiveEncoding.RankedBranchRun
#print axioms EffectiveEncoding.RankedBranchRun
#check EffectiveEncoding.rankedIndexedRun
#print axioms EffectiveEncoding.rankedIndexedRun
#check EffectiveEncoding.rankedBranchRun
#print axioms EffectiveEncoding.rankedBranchRun
#check EffectiveEncoding.RankedAlignmentRun
#print axioms EffectiveEncoding.RankedAlignmentRun
#check EffectiveEncoding.rankedAlignmentRun
#print axioms EffectiveEncoding.rankedAlignmentRun
#check EffectiveEncoding.encodedPivotEndpoint
#print axioms EffectiveEncoding.encodedPivotEndpoint
#check EffectiveEncoding.rankedBranchTableRun
#print axioms EffectiveEncoding.rankedBranchTableRun
#check EffectiveEncoding.rankedOccupationRun
#print axioms EffectiveEncoding.rankedOccupationRun
#check EffectiveEncoding.rankedStageRun
#print axioms EffectiveEncoding.rankedStageRun
#check EffectiveEncoding.rankedCompressionRun
#print axioms EffectiveEncoding.rankedCompressionRun
#check EffectiveEncoding.rankedDescriptorRun
#print axioms EffectiveEncoding.rankedDescriptorRun
#check EffectiveEncoding.RankedLabelRun
#print axioms EffectiveEncoding.RankedLabelRun
#check EffectiveEncoding.rankedExtractionRun
#print axioms EffectiveEncoding.rankedExtractionRun
