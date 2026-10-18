import EffectiveEncoding.CarriedRankExtraction

open Lean Elab Command
namespace EffectiveEncodingCarriedRankVerification

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

end EffectiveEncodingCarriedRankVerification

run_cmd (EffectiveEncodingCarriedRankVerification.checkKinds [
  ``EffectiveEncoding.carriedTripleRankProgram_toTriple,
  ``EffectiveEncoding.carriedEncodedEndpoint_toTriple,
  ``EffectiveEncoding.carriedEncodedEndpoint_eq,
  ``EffectiveEncoding.carriedEncodedEndpoint_value,
  ``EffectiveEncoding.carriedEncodedEndpoint_work,
  ``EffectiveEncoding.carriedOccupationLiteral_value,
  ``EffectiveEncoding.carriedOccupationTable_values,
  ``EffectiveEncoding.erasedTriple_toTriple,
  ``EffectiveEncoding.carriedMass_value,
  ``EffectiveEncoding.carriedBranchEndpoint_eq,
  ``EffectiveEncoding.carriedNextEndpoint_eq,
  ``EffectiveEncoding.carriedPivotEndpoint_eq,
  ``EffectiveEncoding.carriedBranchRun_eq,
  ``EffectiveEncoding.rankedAlignmentRun_map_result,
  ``EffectiveEncoding.carriedAlignmentRun_result,
  ``EffectiveEncoding.carriedAlignmentRun_work,
  ``EffectiveEncoding.carriedBranchTableRun_eq,
  ``EffectiveEncoding.rankedAlignmentRun_map_eq,
  ``EffectiveEncoding.carriedAlignmentRun_eq,
  ``EffectiveEncoding.carriedOccupationRun_eq,
  ``EffectiveEncoding.carriedStageRun_eq,
  ``EffectiveEncoding.carriedCompressionRun_eq,
  ``EffectiveEncoding.carriedDescriptorRun_eq,
  ``EffectiveEncoding.carriedDescriptorRun_work,
  ``EffectiveEncoding.carriedRankExtractionRun_eq,
  ``EffectiveEncoding.carriedRankExtractionRun_word,
  ``EffectiveEncoding.carriedRankExtractionRun_work,
  ``EffectiveEncoding.carriedRankExtractionRun_fidelity
] [
  ``EffectiveEncoding.carriedTripleRankProgram,
  ``EffectiveEncoding.carriedEncodedEndpoint,
  ``EffectiveEncoding.CarriedOccupation,
  ``EffectiveEncoding.carriedOccupationLiteral,
  ``EffectiveEncoding.carriedOccupationTable,
  ``EffectiveEncoding.erasedTriple,
  ``EffectiveEncoding.carriedMass,
  ``EffectiveEncoding.carriedBranchEndpoint,
  ``EffectiveEncoding.carriedNextEndpoint,
  ``EffectiveEncoding.carriedPivotEndpoint,
  ``EffectiveEncoding.carriedBranchRun,
  ``EffectiveEncoding.carriedAlignmentRun,
  ``EffectiveEncoding.carriedBranchTableRun,
  ``EffectiveEncoding.carriedOccupationRun,
  ``EffectiveEncoding.carriedStageRun,
  ``EffectiveEncoding.carriedCompressionRun,
  ``EffectiveEncoding.carriedDescriptorRun,
  ``EffectiveEncoding.carriedRankExtractionRun
])

#check EffectiveEncoding.carriedTripleRankProgram_toTriple
#print axioms EffectiveEncoding.carriedTripleRankProgram_toTriple
#check EffectiveEncoding.carriedEncodedEndpoint_toTriple
#print axioms EffectiveEncoding.carriedEncodedEndpoint_toTriple
#check EffectiveEncoding.carriedEncodedEndpoint_eq
#print axioms EffectiveEncoding.carriedEncodedEndpoint_eq
#check EffectiveEncoding.carriedEncodedEndpoint_value
#print axioms EffectiveEncoding.carriedEncodedEndpoint_value
#check EffectiveEncoding.carriedEncodedEndpoint_work
#print axioms EffectiveEncoding.carriedEncodedEndpoint_work
#check EffectiveEncoding.carriedOccupationLiteral_value
#print axioms EffectiveEncoding.carriedOccupationLiteral_value
#check EffectiveEncoding.carriedOccupationTable_values
#print axioms EffectiveEncoding.carriedOccupationTable_values
#check EffectiveEncoding.erasedTriple_toTriple
#print axioms EffectiveEncoding.erasedTriple_toTriple
#check EffectiveEncoding.carriedMass_value
#print axioms EffectiveEncoding.carriedMass_value
#check EffectiveEncoding.carriedBranchEndpoint_eq
#print axioms EffectiveEncoding.carriedBranchEndpoint_eq
#check EffectiveEncoding.carriedNextEndpoint_eq
#print axioms EffectiveEncoding.carriedNextEndpoint_eq
#check EffectiveEncoding.carriedPivotEndpoint_eq
#print axioms EffectiveEncoding.carriedPivotEndpoint_eq
#check EffectiveEncoding.carriedBranchRun_eq
#print axioms EffectiveEncoding.carriedBranchRun_eq
#check EffectiveEncoding.rankedAlignmentRun_map_result
#print axioms EffectiveEncoding.rankedAlignmentRun_map_result
#check EffectiveEncoding.carriedAlignmentRun_result
#print axioms EffectiveEncoding.carriedAlignmentRun_result
#check EffectiveEncoding.carriedAlignmentRun_work
#print axioms EffectiveEncoding.carriedAlignmentRun_work
#check EffectiveEncoding.carriedBranchTableRun_eq
#print axioms EffectiveEncoding.carriedBranchTableRun_eq
#check EffectiveEncoding.rankedAlignmentRun_map_eq
#print axioms EffectiveEncoding.rankedAlignmentRun_map_eq
#check EffectiveEncoding.carriedAlignmentRun_eq
#print axioms EffectiveEncoding.carriedAlignmentRun_eq
#check EffectiveEncoding.carriedOccupationRun_eq
#print axioms EffectiveEncoding.carriedOccupationRun_eq
#check EffectiveEncoding.carriedStageRun_eq
#print axioms EffectiveEncoding.carriedStageRun_eq
#check EffectiveEncoding.carriedCompressionRun_eq
#print axioms EffectiveEncoding.carriedCompressionRun_eq
#check EffectiveEncoding.carriedDescriptorRun_eq
#print axioms EffectiveEncoding.carriedDescriptorRun_eq
#check EffectiveEncoding.carriedDescriptorRun_work
#print axioms EffectiveEncoding.carriedDescriptorRun_work
#check EffectiveEncoding.carriedRankExtractionRun_eq
#print axioms EffectiveEncoding.carriedRankExtractionRun_eq
#check EffectiveEncoding.carriedRankExtractionRun_word
#print axioms EffectiveEncoding.carriedRankExtractionRun_word
#check EffectiveEncoding.carriedRankExtractionRun_work
#print axioms EffectiveEncoding.carriedRankExtractionRun_work
#check EffectiveEncoding.carriedRankExtractionRun_fidelity
#print axioms EffectiveEncoding.carriedRankExtractionRun_fidelity
#check EffectiveEncoding.carriedTripleRankProgram
#print axioms EffectiveEncoding.carriedTripleRankProgram
#check EffectiveEncoding.carriedEncodedEndpoint
#print axioms EffectiveEncoding.carriedEncodedEndpoint
#check EffectiveEncoding.CarriedOccupation
#print axioms EffectiveEncoding.CarriedOccupation
#check EffectiveEncoding.carriedOccupationLiteral
#print axioms EffectiveEncoding.carriedOccupationLiteral
#check EffectiveEncoding.carriedOccupationTable
#print axioms EffectiveEncoding.carriedOccupationTable
#check EffectiveEncoding.erasedTriple
#print axioms EffectiveEncoding.erasedTriple
#check EffectiveEncoding.carriedMass
#print axioms EffectiveEncoding.carriedMass
#check EffectiveEncoding.carriedBranchEndpoint
#print axioms EffectiveEncoding.carriedBranchEndpoint
#check EffectiveEncoding.carriedNextEndpoint
#print axioms EffectiveEncoding.carriedNextEndpoint
#check EffectiveEncoding.carriedPivotEndpoint
#print axioms EffectiveEncoding.carriedPivotEndpoint
#check EffectiveEncoding.carriedBranchRun
#print axioms EffectiveEncoding.carriedBranchRun
#check EffectiveEncoding.carriedAlignmentRun
#print axioms EffectiveEncoding.carriedAlignmentRun
#check EffectiveEncoding.carriedBranchTableRun
#print axioms EffectiveEncoding.carriedBranchTableRun
#check EffectiveEncoding.carriedOccupationRun
#print axioms EffectiveEncoding.carriedOccupationRun
#check EffectiveEncoding.carriedStageRun
#print axioms EffectiveEncoding.carriedStageRun
#check EffectiveEncoding.carriedCompressionRun
#print axioms EffectiveEncoding.carriedCompressionRun
#check EffectiveEncoding.carriedDescriptorRun
#print axioms EffectiveEncoding.carriedDescriptorRun
#check EffectiveEncoding.carriedRankExtractionRun
#print axioms EffectiveEncoding.carriedRankExtractionRun
