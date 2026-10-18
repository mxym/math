import EffectiveEncoding.ConstructiveRankExtraction

open Lean Elab Command
namespace EffectiveEncodingConstructiveRankVerification

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

end EffectiveEncodingConstructiveRankVerification

run_cmd (EffectiveEncodingConstructiveRankVerification.checkKinds [
  ``EffectiveEncoding.rangeBuild_items,
  ``EffectiveEncoding.rangeBuild_steps,
  ``EffectiveEncoding.productRowBuild_items,
  ``EffectiveEncoding.productRowBuild_steps,
  ``EffectiveEncoding.productBuild_items,
  ``EffectiveEncoding.productBuild_steps,
  ``EffectiveEncoding.filterBuild_items,
  ``EffectiveEncoding.filterBuild_steps,
  ``EffectiveEncoding.filterBuild_queries,
  ``EffectiveEncoding.triplesBuild_items,
  ``EffectiveEncoding.triplesBuild_queries,
  ``EffectiveEncoding.triplesBuild_steps,
  ``EffectiveEncoding.rankByConstructiveTriples_eq,
  ``EffectiveEncoding.constructiveRankProgram_constructionSteps,
  ``EffectiveEncoding.constructiveRankProgram_predicateQueries,
  ``EffectiveEncoding.constructiveRankProgram_natEqualityQueries,
  ``EffectiveEncoding.constructedCompactEncoding_eq,
  ``EffectiveEncoding.constructedNextEncoding_eq,
  ``EffectiveEncoding.builtOccupations_eq,
  ``EffectiveEncoding.builtPackedOccupationStepCode_eq,
  ``EffectiveEncoding.constructedStageCode_eq,
  ``EffectiveEncoding.constructedCompressionCode_eq,
  ``EffectiveEncoding.constructedExtractionCode_eq,
  ``EffectiveEncoding.constructiveRankExtractionCode_eq,
  ``EffectiveEncoding.constructiveRankExtractionCode_fidelity
] [
  ``EffectiveEncoding.ListBuild,
  ``EffectiveEncoding.ListBuild.empty,
  ``EffectiveEncoding.ListBuild.emit,
  ``EffectiveEncoding.ListBuild.append,
  ``EffectiveEncoding.rangeBuild,
  ``EffectiveEncoding.productRowBuild,
  ``EffectiveEncoding.productBuild,
  ``EffectiveEncoding.FilterBuild,
  ``EffectiveEncoding.filterBuild,
  ``EffectiveEncoding.triplesBuild,
  ``EffectiveEncoding.ConstructiveRankRun,
  ``EffectiveEncoding.constructiveRankProgram,
  ``EffectiveEncoding.rankByConstructiveTriples,
  ``EffectiveEncoding.constructedCompactEncoding,
  ``EffectiveEncoding.constructedNextEncoding,
  ``EffectiveEncoding.builtOccupations,
  ``EffectiveEncoding.builtPackedOccupationStepCode,
  ``EffectiveEncoding.constructedStageCode,
  ``EffectiveEncoding.constructedCompressionCode,
  ``EffectiveEncoding.constructedExtractionCode,
  ``EffectiveEncoding.constructiveRankExtractionCode
])

#check EffectiveEncoding.rangeBuild_items
#print axioms EffectiveEncoding.rangeBuild_items
#check EffectiveEncoding.rangeBuild_steps
#print axioms EffectiveEncoding.rangeBuild_steps
#check EffectiveEncoding.productRowBuild_items
#print axioms EffectiveEncoding.productRowBuild_items
#check EffectiveEncoding.productRowBuild_steps
#print axioms EffectiveEncoding.productRowBuild_steps
#check EffectiveEncoding.productBuild_items
#print axioms EffectiveEncoding.productBuild_items
#check EffectiveEncoding.productBuild_steps
#print axioms EffectiveEncoding.productBuild_steps
#check EffectiveEncoding.filterBuild_items
#print axioms EffectiveEncoding.filterBuild_items
#check EffectiveEncoding.filterBuild_steps
#print axioms EffectiveEncoding.filterBuild_steps
#check EffectiveEncoding.filterBuild_queries
#print axioms EffectiveEncoding.filterBuild_queries
#check EffectiveEncoding.triplesBuild_items
#print axioms EffectiveEncoding.triplesBuild_items
#check EffectiveEncoding.triplesBuild_queries
#print axioms EffectiveEncoding.triplesBuild_queries
#check EffectiveEncoding.triplesBuild_steps
#print axioms EffectiveEncoding.triplesBuild_steps
#check EffectiveEncoding.rankByConstructiveTriples_eq
#print axioms EffectiveEncoding.rankByConstructiveTriples_eq
#check EffectiveEncoding.constructiveRankProgram_constructionSteps
#print axioms EffectiveEncoding.constructiveRankProgram_constructionSteps
#check EffectiveEncoding.constructiveRankProgram_predicateQueries
#print axioms EffectiveEncoding.constructiveRankProgram_predicateQueries
#check EffectiveEncoding.constructiveRankProgram_natEqualityQueries
#print axioms EffectiveEncoding.constructiveRankProgram_natEqualityQueries
#check EffectiveEncoding.constructedCompactEncoding_eq
#print axioms EffectiveEncoding.constructedCompactEncoding_eq
#check EffectiveEncoding.constructedNextEncoding_eq
#print axioms EffectiveEncoding.constructedNextEncoding_eq
#check EffectiveEncoding.builtOccupations_eq
#print axioms EffectiveEncoding.builtOccupations_eq
#check EffectiveEncoding.builtPackedOccupationStepCode_eq
#print axioms EffectiveEncoding.builtPackedOccupationStepCode_eq
#check EffectiveEncoding.constructedStageCode_eq
#print axioms EffectiveEncoding.constructedStageCode_eq
#check EffectiveEncoding.constructedCompressionCode_eq
#print axioms EffectiveEncoding.constructedCompressionCode_eq
#check EffectiveEncoding.constructedExtractionCode_eq
#print axioms EffectiveEncoding.constructedExtractionCode_eq
#check EffectiveEncoding.constructiveRankExtractionCode_eq
#print axioms EffectiveEncoding.constructiveRankExtractionCode_eq
#check EffectiveEncoding.constructiveRankExtractionCode_fidelity
#print axioms EffectiveEncoding.constructiveRankExtractionCode_fidelity
#check EffectiveEncoding.ListBuild
#print axioms EffectiveEncoding.ListBuild
#check EffectiveEncoding.ListBuild.empty
#print axioms EffectiveEncoding.ListBuild.empty
#check EffectiveEncoding.ListBuild.emit
#print axioms EffectiveEncoding.ListBuild.emit
#check EffectiveEncoding.ListBuild.append
#print axioms EffectiveEncoding.ListBuild.append
#check EffectiveEncoding.rangeBuild
#print axioms EffectiveEncoding.rangeBuild
#check EffectiveEncoding.productRowBuild
#print axioms EffectiveEncoding.productRowBuild
#check EffectiveEncoding.productBuild
#print axioms EffectiveEncoding.productBuild
#check EffectiveEncoding.FilterBuild
#print axioms EffectiveEncoding.FilterBuild
#check EffectiveEncoding.filterBuild
#print axioms EffectiveEncoding.filterBuild
#check EffectiveEncoding.triplesBuild
#print axioms EffectiveEncoding.triplesBuild
#check EffectiveEncoding.ConstructiveRankRun
#print axioms EffectiveEncoding.ConstructiveRankRun
#check EffectiveEncoding.constructiveRankProgram
#print axioms EffectiveEncoding.constructiveRankProgram
#check EffectiveEncoding.rankByConstructiveTriples
#print axioms EffectiveEncoding.rankByConstructiveTriples
#check EffectiveEncoding.constructedCompactEncoding
#print axioms EffectiveEncoding.constructedCompactEncoding
#check EffectiveEncoding.constructedNextEncoding
#print axioms EffectiveEncoding.constructedNextEncoding
#check EffectiveEncoding.builtOccupations
#print axioms EffectiveEncoding.builtOccupations
#check EffectiveEncoding.builtPackedOccupationStepCode
#print axioms EffectiveEncoding.builtPackedOccupationStepCode
#check EffectiveEncoding.constructedStageCode
#print axioms EffectiveEncoding.constructedStageCode
#check EffectiveEncoding.constructedCompressionCode
#print axioms EffectiveEncoding.constructedCompressionCode
#check EffectiveEncoding.constructedExtractionCode
#print axioms EffectiveEncoding.constructedExtractionCode
#check EffectiveEncoding.constructiveRankExtractionCode
#print axioms EffectiveEncoding.constructiveRankExtractionCode
