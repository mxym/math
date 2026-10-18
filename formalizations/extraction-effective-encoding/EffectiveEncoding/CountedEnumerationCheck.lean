import EffectiveEncoding.CountedEnumeration

open Lean Elab Command
namespace EffectiveEncodingCountedEnumerationVerification

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

end EffectiveEncodingCountedEnumerationVerification

run_cmd (EffectiveEncodingCountedEnumerationVerification.checkKinds [
  ``EffectiveEncoding.filterWithQueries_erase,
  ``EffectiveEncoding.filterWithQueries_queries,
  ``EffectiveEncoding.countedTriples_erase,
  ``EffectiveEncoding.countedTriples_queries,
  ``EffectiveEncoding.occupationList_congr,
  ``EffectiveEncoding.countedOccupations_erase,
  ``EffectiveEncoding.countedOccupations_queries,
  ``EffectiveEncoding.countedOccupations_constructorCalls,
  ``EffectiveEncoding.countedOccupations_constructorCalls_bound,
  ``EffectiveEncoding.indexWithQueries_erase,
  ``EffectiveEncoding.indexWithQueries_queries,
  ``EffectiveEncoding.countedRank_erase,
  ``EffectiveEncoding.countedRank_candidateQueries,
  ``EffectiveEncoding.countedRank_equalityQueries,
  ``EffectiveEncoding.countedRank_equalityQueries_polynomial
] [
  ``EffectiveEncoding.filterWithQueries,
  ``EffectiveEncoding.countedTriples,
  ``EffectiveEncoding.occupationList,
  ``EffectiveEncoding.countedOccupations,
  ``EffectiveEncoding.indexWithQueries,
  ``EffectiveEncoding.RankRun,
  ``EffectiveEncoding.countedRank
])

#check EffectiveEncoding.filterWithQueries_erase
#print axioms EffectiveEncoding.filterWithQueries_erase
#check EffectiveEncoding.filterWithQueries_queries
#print axioms EffectiveEncoding.filterWithQueries_queries
#check EffectiveEncoding.countedTriples_erase
#print axioms EffectiveEncoding.countedTriples_erase
#check EffectiveEncoding.countedTriples_queries
#print axioms EffectiveEncoding.countedTriples_queries
#check EffectiveEncoding.occupationList_congr
#print axioms EffectiveEncoding.occupationList_congr
#check EffectiveEncoding.countedOccupations_erase
#print axioms EffectiveEncoding.countedOccupations_erase
#check EffectiveEncoding.countedOccupations_queries
#print axioms EffectiveEncoding.countedOccupations_queries
#check EffectiveEncoding.countedOccupations_constructorCalls
#print axioms EffectiveEncoding.countedOccupations_constructorCalls
#check EffectiveEncoding.countedOccupations_constructorCalls_bound
#print axioms EffectiveEncoding.countedOccupations_constructorCalls_bound
#check EffectiveEncoding.indexWithQueries_erase
#print axioms EffectiveEncoding.indexWithQueries_erase
#check EffectiveEncoding.indexWithQueries_queries
#print axioms EffectiveEncoding.indexWithQueries_queries
#check EffectiveEncoding.countedRank_erase
#print axioms EffectiveEncoding.countedRank_erase
#check EffectiveEncoding.countedRank_candidateQueries
#print axioms EffectiveEncoding.countedRank_candidateQueries
#check EffectiveEncoding.countedRank_equalityQueries
#print axioms EffectiveEncoding.countedRank_equalityQueries
#check EffectiveEncoding.countedRank_equalityQueries_polynomial
#print axioms EffectiveEncoding.countedRank_equalityQueries_polynomial
#check EffectiveEncoding.filterWithQueries
#print axioms EffectiveEncoding.filterWithQueries
#check EffectiveEncoding.countedTriples
#print axioms EffectiveEncoding.countedTriples
#check EffectiveEncoding.occupationList
#print axioms EffectiveEncoding.occupationList
#check EffectiveEncoding.countedOccupations
#print axioms EffectiveEncoding.countedOccupations
#check EffectiveEncoding.indexWithQueries
#print axioms EffectiveEncoding.indexWithQueries
#check EffectiveEncoding.RankRun
#print axioms EffectiveEncoding.RankRun
#check EffectiveEncoding.countedRank
#print axioms EffectiveEncoding.countedRank
