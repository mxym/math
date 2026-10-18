import EffectiveEncoding.LiteralOccupationExtraction

open Lean Elab Command
namespace EffectiveEncodingLiteralOccupationVerification

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

end EffectiveEncodingLiteralOccupationVerification

run_cmd (EffectiveEncodingLiteralOccupationVerification.checkKinds [
  ``EffectiveEncoding.replicateBuild_items,
  ``EffectiveEncoding.replicateBuild_steps,
  ``EffectiveEncoding.occupationLettersBuild_items,
  ``EffectiveEncoding.occupationLettersBuild_length,
  ``EffectiveEncoding.occupationLettersBuild_steps,
  ``EffectiveEncoding.occupationLiteralProgram_value,
  ``EffectiveEncoding.occupationLiteralProgram_steps,
  ``EffectiveEncoding.triplesBuild_total,
  ``EffectiveEncoding.literalOccupationTable_value,
  ``EffectiveEncoding.literalOccupationTable_tripleSteps,
  ``EffectiveEncoding.literalOccupationTable_literalSteps,
  ``EffectiveEncoding.literalPackedOccupationStepCode_eq,
  ``EffectiveEncoding.literalStageCode_eq,
  ``EffectiveEncoding.literalCompressionCode_eq,
  ``EffectiveEncoding.literalExtractionCode_eq,
  ``EffectiveEncoding.literalOccupationExtractionCode_eq,
  ``EffectiveEncoding.literalOccupationExtractionCode_fidelity,
  ``EffectiveEncoding.extractionOccupationLiteralSteps_bound,
  ``EffectiveEncoding.extractionOccupationTripleSteps_bound
] [
  ``EffectiveEncoding.replicateBuild,
  ``EffectiveEncoding.occupationLettersBuild,
  ``EffectiveEncoding.OccupationLiteralResult,
  ``EffectiveEncoding.occupationLiteralProgram,
  ``EffectiveEncoding.LiteralOccupationTable,
  ``EffectiveEncoding.literalOccupationTable,
  ``EffectiveEncoding.literalPackedOccupationStepCode,
  ``EffectiveEncoding.literalStageCode,
  ``EffectiveEncoding.literalCompressionCode,
  ``EffectiveEncoding.literalExtractionCode,
  ``EffectiveEncoding.literalOccupationExtractionCode,
  ``EffectiveEncoding.extractionOccupationLiteralSteps,
  ``EffectiveEncoding.extractionOccupationTripleSteps
])

#check EffectiveEncoding.replicateBuild_items
#print axioms EffectiveEncoding.replicateBuild_items
#check EffectiveEncoding.replicateBuild_steps
#print axioms EffectiveEncoding.replicateBuild_steps
#check EffectiveEncoding.occupationLettersBuild_items
#print axioms EffectiveEncoding.occupationLettersBuild_items
#check EffectiveEncoding.occupationLettersBuild_length
#print axioms EffectiveEncoding.occupationLettersBuild_length
#check EffectiveEncoding.occupationLettersBuild_steps
#print axioms EffectiveEncoding.occupationLettersBuild_steps
#check EffectiveEncoding.occupationLiteralProgram_value
#print axioms EffectiveEncoding.occupationLiteralProgram_value
#check EffectiveEncoding.occupationLiteralProgram_steps
#print axioms EffectiveEncoding.occupationLiteralProgram_steps
#check EffectiveEncoding.triplesBuild_total
#print axioms EffectiveEncoding.triplesBuild_total
#check EffectiveEncoding.literalOccupationTable_value
#print axioms EffectiveEncoding.literalOccupationTable_value
#check EffectiveEncoding.literalOccupationTable_tripleSteps
#print axioms EffectiveEncoding.literalOccupationTable_tripleSteps
#check EffectiveEncoding.literalOccupationTable_literalSteps
#print axioms EffectiveEncoding.literalOccupationTable_literalSteps
#check EffectiveEncoding.literalPackedOccupationStepCode_eq
#print axioms EffectiveEncoding.literalPackedOccupationStepCode_eq
#check EffectiveEncoding.literalStageCode_eq
#print axioms EffectiveEncoding.literalStageCode_eq
#check EffectiveEncoding.literalCompressionCode_eq
#print axioms EffectiveEncoding.literalCompressionCode_eq
#check EffectiveEncoding.literalExtractionCode_eq
#print axioms EffectiveEncoding.literalExtractionCode_eq
#check EffectiveEncoding.literalOccupationExtractionCode_eq
#print axioms EffectiveEncoding.literalOccupationExtractionCode_eq
#check EffectiveEncoding.literalOccupationExtractionCode_fidelity
#print axioms EffectiveEncoding.literalOccupationExtractionCode_fidelity
#check EffectiveEncoding.extractionOccupationLiteralSteps_bound
#print axioms EffectiveEncoding.extractionOccupationLiteralSteps_bound
#check EffectiveEncoding.extractionOccupationTripleSteps_bound
#print axioms EffectiveEncoding.extractionOccupationTripleSteps_bound
#check EffectiveEncoding.replicateBuild
#print axioms EffectiveEncoding.replicateBuild
#check EffectiveEncoding.occupationLettersBuild
#print axioms EffectiveEncoding.occupationLettersBuild
#check EffectiveEncoding.OccupationLiteralResult
#print axioms EffectiveEncoding.OccupationLiteralResult
#check EffectiveEncoding.occupationLiteralProgram
#print axioms EffectiveEncoding.occupationLiteralProgram
#check EffectiveEncoding.LiteralOccupationTable
#print axioms EffectiveEncoding.LiteralOccupationTable
#check EffectiveEncoding.literalOccupationTable
#print axioms EffectiveEncoding.literalOccupationTable
#check EffectiveEncoding.literalPackedOccupationStepCode
#print axioms EffectiveEncoding.literalPackedOccupationStepCode
#check EffectiveEncoding.literalStageCode
#print axioms EffectiveEncoding.literalStageCode
#check EffectiveEncoding.literalCompressionCode
#print axioms EffectiveEncoding.literalCompressionCode
#check EffectiveEncoding.literalExtractionCode
#print axioms EffectiveEncoding.literalExtractionCode
#check EffectiveEncoding.literalOccupationExtractionCode
#print axioms EffectiveEncoding.literalOccupationExtractionCode
#check EffectiveEncoding.extractionOccupationLiteralSteps
#print axioms EffectiveEncoding.extractionOccupationLiteralSteps
#check EffectiveEncoding.extractionOccupationTripleSteps
#print axioms EffectiveEncoding.extractionOccupationTripleSteps
