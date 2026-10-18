import EffectiveEncoding.PackedEndpointExtraction

open Lean Elab Command
namespace EffectiveEncodingPackedEndpointVerification

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

end EffectiveEncodingPackedEndpointVerification

run_cmd (EffectiveEncodingPackedEndpointVerification.checkKinds [
  ``EffectiveEncoding.unpackBits_packBits,
  ``EffectiveEncoding.packBits_unpackBits,
  ``EffectiveEncoding.unpackBits_injective,
  ``EffectiveEncoding.map_swap_of_injective,
  ``EffectiveEncoding.applyPackedSwaps_value,
  ``EffectiveEncoding.applyPackedSwaps_count,
  ``EffectiveEncoding.packedAlignmentRun_word,
  ``EffectiveEncoding.packedAlignmentRun_coordinates,
  ``EffectiveEncoding.packedAlignmentRun_count,
  ``EffectiveEncoding.packedOccupationStepCode_eq,
  ``EffectiveEncoding.packedStageCode_eq,
  ``EffectiveEncoding.packedCompressionCode_eq,
  ``EffectiveEncoding.packedExtractionCode_eq,
  ``EffectiveEncoding.packedEndpointExtractionCode_eq,
  ``EffectiveEncoding.packedEndpointExtractionCode_fidelity,
  ``EffectiveEncoding.stagePackedEndpointCoordinates_exact,
  ``EffectiveEncoding.stagePackedEndpointCoordinates_bound,
  ``EffectiveEncoding.extractionPackedEndpointCoordinates_bound
] [
  ``EffectiveEncoding.PackedBits,
  ``EffectiveEncoding.packBits,
  ``EffectiveEncoding.unpackBits,
  ``EffectiveEncoding.packedStackBits,
  ``EffectiveEncoding.applyPackedSwaps,
  ``EffectiveEncoding.PackedAlignmentRun,
  ``EffectiveEncoding.packedAlignmentRun,
  ``EffectiveEncoding.packedOccupationStepCode,
  ``EffectiveEncoding.packedStageCode,
  ``EffectiveEncoding.packedCompressionCode,
  ``EffectiveEncoding.packedExtractionCode,
  ``EffectiveEncoding.packedEndpointExtractionCode,
  ``EffectiveEncoding.stagePackedEndpointCoordinates,
  ``EffectiveEncoding.extractionPackedEndpointCoordinates
])

#check EffectiveEncoding.unpackBits_packBits
#print axioms EffectiveEncoding.unpackBits_packBits
#check EffectiveEncoding.packBits_unpackBits
#print axioms EffectiveEncoding.packBits_unpackBits
#check EffectiveEncoding.unpackBits_injective
#print axioms EffectiveEncoding.unpackBits_injective
#check EffectiveEncoding.map_swap_of_injective
#print axioms EffectiveEncoding.map_swap_of_injective
#check EffectiveEncoding.applyPackedSwaps_value
#print axioms EffectiveEncoding.applyPackedSwaps_value
#check EffectiveEncoding.applyPackedSwaps_count
#print axioms EffectiveEncoding.applyPackedSwaps_count
#check EffectiveEncoding.packedAlignmentRun_word
#print axioms EffectiveEncoding.packedAlignmentRun_word
#check EffectiveEncoding.packedAlignmentRun_coordinates
#print axioms EffectiveEncoding.packedAlignmentRun_coordinates
#check EffectiveEncoding.packedAlignmentRun_count
#print axioms EffectiveEncoding.packedAlignmentRun_count
#check EffectiveEncoding.packedOccupationStepCode_eq
#print axioms EffectiveEncoding.packedOccupationStepCode_eq
#check EffectiveEncoding.packedStageCode_eq
#print axioms EffectiveEncoding.packedStageCode_eq
#check EffectiveEncoding.packedCompressionCode_eq
#print axioms EffectiveEncoding.packedCompressionCode_eq
#check EffectiveEncoding.packedExtractionCode_eq
#print axioms EffectiveEncoding.packedExtractionCode_eq
#check EffectiveEncoding.packedEndpointExtractionCode_eq
#print axioms EffectiveEncoding.packedEndpointExtractionCode_eq
#check EffectiveEncoding.packedEndpointExtractionCode_fidelity
#print axioms EffectiveEncoding.packedEndpointExtractionCode_fidelity
#check EffectiveEncoding.stagePackedEndpointCoordinates_exact
#print axioms EffectiveEncoding.stagePackedEndpointCoordinates_exact
#check EffectiveEncoding.stagePackedEndpointCoordinates_bound
#print axioms EffectiveEncoding.stagePackedEndpointCoordinates_bound
#check EffectiveEncoding.extractionPackedEndpointCoordinates_bound
#print axioms EffectiveEncoding.extractionPackedEndpointCoordinates_bound
#check EffectiveEncoding.PackedBits
#print axioms EffectiveEncoding.PackedBits
#check EffectiveEncoding.packBits
#print axioms EffectiveEncoding.packBits
#check EffectiveEncoding.unpackBits
#print axioms EffectiveEncoding.unpackBits
#check EffectiveEncoding.packedStackBits
#print axioms EffectiveEncoding.packedStackBits
#check EffectiveEncoding.applyPackedSwaps
#print axioms EffectiveEncoding.applyPackedSwaps
#check EffectiveEncoding.PackedAlignmentRun
#print axioms EffectiveEncoding.PackedAlignmentRun
#check EffectiveEncoding.packedAlignmentRun
#print axioms EffectiveEncoding.packedAlignmentRun
#check EffectiveEncoding.packedOccupationStepCode
#print axioms EffectiveEncoding.packedOccupationStepCode
#check EffectiveEncoding.packedStageCode
#print axioms EffectiveEncoding.packedStageCode
#check EffectiveEncoding.packedCompressionCode
#print axioms EffectiveEncoding.packedCompressionCode
#check EffectiveEncoding.packedExtractionCode
#print axioms EffectiveEncoding.packedExtractionCode
#check EffectiveEncoding.packedEndpointExtractionCode
#print axioms EffectiveEncoding.packedEndpointExtractionCode
#check EffectiveEncoding.stagePackedEndpointCoordinates
#print axioms EffectiveEncoding.stagePackedEndpointCoordinates
#check EffectiveEncoding.extractionPackedEndpointCoordinates
#print axioms EffectiveEncoding.extractionPackedEndpointCoordinates
