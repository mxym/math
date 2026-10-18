import EffectiveEncoding.TripleRankExtraction

open Lean Elab Command
namespace EffectiveEncodingTripleRankVerification

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

end EffectiveEncodingTripleRankVerification

run_cmd (EffectiveEncodingTripleRankVerification.checkKinds [
  ``EffectiveEncoding.tripleEqualityRun_value,
  ``EffectiveEncoding.tripleEqualityRun_count,
  ``EffectiveEncoding.indexTriplesWithQueries_value,
  ``EffectiveEncoding.indexTriplesWithQueries_count,
  ``EffectiveEncoding.toTriple_injective,
  ``EffectiveEncoding.occupations_toTriple,
  ``EffectiveEncoding.idxOf_map_injective,
  ``EffectiveEncoding.triples_length,
  ``EffectiveEncoding.rankByTriples_eq,
  ``EffectiveEncoding.tripleRankProgram_predicateQueries,
  ``EffectiveEncoding.tripleRankProgram_natEqualityQueries,
  ``EffectiveEncoding.tripleCompactEncoding_eq,
  ``EffectiveEncoding.tripleNextEncoding_eq,
  ``EffectiveEncoding.tripleStoredStageCode_eq,
  ``EffectiveEncoding.tripleStoredCompressionCode_eq,
  ``EffectiveEncoding.tripleStoredExtractionCode_eq,
  ``EffectiveEncoding.tripleRankExtractionCode_eq,
  ``EffectiveEncoding.tripleRankExtractionCode_fidelity
] [
  ``EffectiveEncoding.tripleEqualityRun,
  ``EffectiveEncoding.indexTriplesWithQueries,
  ``EffectiveEncoding.TripleRankRun,
  ``EffectiveEncoding.tripleRankProgram,
  ``EffectiveEncoding.rankByTriples,
  ``EffectiveEncoding.tripleCompactEncoding,
  ``EffectiveEncoding.tripleNextEncoding,
  ``EffectiveEncoding.tripleStoredStageCode,
  ``EffectiveEncoding.tripleStoredCompressionCode,
  ``EffectiveEncoding.tripleStoredExtractionCode,
  ``EffectiveEncoding.tripleRankExtractionCode
])

#check EffectiveEncoding.tripleEqualityRun_value
#print axioms EffectiveEncoding.tripleEqualityRun_value
#check EffectiveEncoding.tripleEqualityRun_count
#print axioms EffectiveEncoding.tripleEqualityRun_count
#check EffectiveEncoding.indexTriplesWithQueries_value
#print axioms EffectiveEncoding.indexTriplesWithQueries_value
#check EffectiveEncoding.indexTriplesWithQueries_count
#print axioms EffectiveEncoding.indexTriplesWithQueries_count
#check EffectiveEncoding.toTriple_injective
#print axioms EffectiveEncoding.toTriple_injective
#check EffectiveEncoding.occupations_toTriple
#print axioms EffectiveEncoding.occupations_toTriple
#check EffectiveEncoding.idxOf_map_injective
#print axioms EffectiveEncoding.idxOf_map_injective
#check EffectiveEncoding.triples_length
#print axioms EffectiveEncoding.triples_length
#check EffectiveEncoding.rankByTriples_eq
#print axioms EffectiveEncoding.rankByTriples_eq
#check EffectiveEncoding.tripleRankProgram_predicateQueries
#print axioms EffectiveEncoding.tripleRankProgram_predicateQueries
#check EffectiveEncoding.tripleRankProgram_natEqualityQueries
#print axioms EffectiveEncoding.tripleRankProgram_natEqualityQueries
#check EffectiveEncoding.tripleCompactEncoding_eq
#print axioms EffectiveEncoding.tripleCompactEncoding_eq
#check EffectiveEncoding.tripleNextEncoding_eq
#print axioms EffectiveEncoding.tripleNextEncoding_eq
#check EffectiveEncoding.tripleStoredStageCode_eq
#print axioms EffectiveEncoding.tripleStoredStageCode_eq
#check EffectiveEncoding.tripleStoredCompressionCode_eq
#print axioms EffectiveEncoding.tripleStoredCompressionCode_eq
#check EffectiveEncoding.tripleStoredExtractionCode_eq
#print axioms EffectiveEncoding.tripleStoredExtractionCode_eq
#check EffectiveEncoding.tripleRankExtractionCode_eq
#print axioms EffectiveEncoding.tripleRankExtractionCode_eq
#check EffectiveEncoding.tripleRankExtractionCode_fidelity
#print axioms EffectiveEncoding.tripleRankExtractionCode_fidelity
#check EffectiveEncoding.tripleEqualityRun
#print axioms EffectiveEncoding.tripleEqualityRun
#check EffectiveEncoding.indexTriplesWithQueries
#print axioms EffectiveEncoding.indexTriplesWithQueries
#check EffectiveEncoding.TripleRankRun
#print axioms EffectiveEncoding.TripleRankRun
#check EffectiveEncoding.tripleRankProgram
#print axioms EffectiveEncoding.tripleRankProgram
#check EffectiveEncoding.rankByTriples
#print axioms EffectiveEncoding.rankByTriples
#check EffectiveEncoding.tripleCompactEncoding
#print axioms EffectiveEncoding.tripleCompactEncoding
#check EffectiveEncoding.tripleNextEncoding
#print axioms EffectiveEncoding.tripleNextEncoding
#check EffectiveEncoding.tripleStoredStageCode
#print axioms EffectiveEncoding.tripleStoredStageCode
#check EffectiveEncoding.tripleStoredCompressionCode
#print axioms EffectiveEncoding.tripleStoredCompressionCode
#check EffectiveEncoding.tripleStoredExtractionCode
#print axioms EffectiveEncoding.tripleStoredExtractionCode
#check EffectiveEncoding.tripleRankExtractionCode
#print axioms EffectiveEncoding.tripleRankExtractionCode
