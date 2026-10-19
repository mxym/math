import EffectiveEncoding.BinaryGeneratedRank
import EffectiveEncoding.BinaryCandidateEvaluation

open Lean Elab Command
namespace EffectiveEncodingBinaryCandidatesVerification

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

end EffectiveEncodingBinaryCandidatesVerification

run_cmd (EffectiveEncodingBinaryCandidatesVerification.checkKinds [
  ``EffectiveEncoding.savedCountSuccessor_exact,
  ``EffectiveEncoding.binaryCountRangeProgram_current,
  ``EffectiveEncoding.binaryCountRangeProgram_items,
  ``EffectiveEncoding.binaryCountRangeProgram_length,
  ``EffectiveEncoding.binaryCountRangeProgram_counts,
  ``EffectiveEncoding.binaryCountRangeProgram_incrementCount,
  ``EffectiveEncoding.binaryCountRangeProgram_incrementTrimActions,
  ``EffectiveEncoding.binaryCountRangeProgram_copyActions,
  ``EffectiveEncoding.binaryCountRangeProgram_actions,
  ``EffectiveEncoding.nativeOrderIsAtMost_correct,
  ``EffectiveEncoding.binaryTripleBoundProgram_accepted,
  ``EffectiveEncoding.binaryTripleBoundProgram_actions,
  ``EffectiveEncoding.binaryCandidateFilterProgram_items,
  ``EffectiveEncoding.binaryCandidateFilterProgram_tests,
  ``EffectiveEncoding.binaryCandidateFilterProgram_predicateActions,
  ``EffectiveEncoding.candidateProductRowProgram_items,
  ``EffectiveEncoding.candidateProductRowProgram_actions,
  ``EffectiveEncoding.candidateProductProgram_items,
  ``EffectiveEncoding.candidateProductProgram_actions,
  ``EffectiveEncoding.candidateProduct_map,
  ``EffectiveEncoding.specSavedTriple_counts,
  ``EffectiveEncoding.specSavedTriple_prepared,
  ``EffectiveEncoding.binaryTriplesProgram_candidates,
  ``EffectiveEncoding.binaryTriplesProgram_candidateLength,
  ``EffectiveEncoding.binaryTriplesProgram_filtered,
  ``EffectiveEncoding.binaryTriplesProgram_counts,
  ``EffectiveEncoding.binaryTriplesProgram_prepared,
  ``EffectiveEncoding.binaryTriplesProgram_tests,
  ``EffectiveEncoding.binaryTriplesProgram_testCount,
  ``EffectiveEncoding.binaryTriplesProgram_candidateWidth,
  ``EffectiveEncoding.binaryTriplesProgram_predicateActions,
  ``EffectiveEncoding.binaryTriplesProgram_actions,
  ``EffectiveEncoding.binaryTriplesProgram_actions_polynomial,
  ``EffectiveEncoding.binaryGeneratedRankProgram_scan,
  ``EffectiveEncoding.binaryGeneratedRankProgram_input,
  ``EffectiveEncoding.binaryGeneratedRankProgram_index,
  ``EffectiveEncoding.binaryGeneratedRankProgram_encoding,
  ``EffectiveEncoding.binaryGeneratedRankProgram_output,
  ``EffectiveEncoding.binaryGeneratedRankProgram_actions,
  ``EffectiveEncoding.binaryGeneratedRankProgram_actions_polynomial
] [
  ``EffectiveEncoding.SavedCountWord,
  ``EffectiveEncoding.savedCountSuccessor,
  ``EffectiveEncoding.BinaryCountRangeResult,
  ``EffectiveEncoding.binaryCountRangeProgram,
  ``EffectiveEncoding.BinaryCountRangeResult.incrementTrimActions,
  ``EffectiveEncoding.BinaryCountRangeResult.actions,
  ``EffectiveEncoding.nativeOrderIsAtMost,
  ``EffectiveEncoding.BinaryTriplePredicateResult,
  ``EffectiveEncoding.binaryTripleBoundProgram,
  ``EffectiveEncoding.BinaryTriplePredicateResult.actions,
  ``EffectiveEncoding.BinaryCandidateFilterResult,
  ``EffectiveEncoding.binaryCandidateFilterProgram,
  ``EffectiveEncoding.BinaryCandidateFilterResult.predicateActions,
  ``EffectiveEncoding.CandidateProductTrace,
  ``EffectiveEncoding.CandidateProductTrace.actions,
  ``EffectiveEncoding.CandidateProductResult,
  ``EffectiveEncoding.candidateProductRowProgram,
  ``EffectiveEncoding.candidateProductProgram,
  ``EffectiveEncoding.SavedTripleWords,
  ``EffectiveEncoding.savedTripleCounts,
  ``EffectiveEncoding.savedTriplePrepared,
  ``EffectiveEncoding.specSavedTriple,
  ``EffectiveEncoding.BinaryTriplesResult,
  ``EffectiveEncoding.binaryTriplesProgram,
  ``EffectiveEncoding.BinaryTriplesResult.actions,
  ``EffectiveEncoding.BinaryGeneratedRankResult,
  ``EffectiveEncoding.binaryGeneratedRankProgram,
  ``EffectiveEncoding.BinaryGeneratedRankResult.actions
])

#check EffectiveEncoding.savedCountSuccessor_exact
#print axioms EffectiveEncoding.savedCountSuccessor_exact
#check EffectiveEncoding.binaryCountRangeProgram_current
#print axioms EffectiveEncoding.binaryCountRangeProgram_current
#check EffectiveEncoding.binaryCountRangeProgram_items
#print axioms EffectiveEncoding.binaryCountRangeProgram_items
#check EffectiveEncoding.binaryCountRangeProgram_length
#print axioms EffectiveEncoding.binaryCountRangeProgram_length
#check EffectiveEncoding.binaryCountRangeProgram_counts
#print axioms EffectiveEncoding.binaryCountRangeProgram_counts
#check EffectiveEncoding.binaryCountRangeProgram_incrementCount
#print axioms EffectiveEncoding.binaryCountRangeProgram_incrementCount
#check EffectiveEncoding.binaryCountRangeProgram_incrementTrimActions
#print axioms EffectiveEncoding.binaryCountRangeProgram_incrementTrimActions
#check EffectiveEncoding.binaryCountRangeProgram_copyActions
#print axioms EffectiveEncoding.binaryCountRangeProgram_copyActions
#check EffectiveEncoding.binaryCountRangeProgram_actions
#print axioms EffectiveEncoding.binaryCountRangeProgram_actions
#check EffectiveEncoding.nativeOrderIsAtMost_correct
#print axioms EffectiveEncoding.nativeOrderIsAtMost_correct
#check EffectiveEncoding.binaryTripleBoundProgram_accepted
#print axioms EffectiveEncoding.binaryTripleBoundProgram_accepted
#check EffectiveEncoding.binaryTripleBoundProgram_actions
#print axioms EffectiveEncoding.binaryTripleBoundProgram_actions
#check EffectiveEncoding.binaryCandidateFilterProgram_items
#print axioms EffectiveEncoding.binaryCandidateFilterProgram_items
#check EffectiveEncoding.binaryCandidateFilterProgram_tests
#print axioms EffectiveEncoding.binaryCandidateFilterProgram_tests
#check EffectiveEncoding.binaryCandidateFilterProgram_predicateActions
#print axioms EffectiveEncoding.binaryCandidateFilterProgram_predicateActions
#check EffectiveEncoding.candidateProductRowProgram_items
#print axioms EffectiveEncoding.candidateProductRowProgram_items
#check EffectiveEncoding.candidateProductRowProgram_actions
#print axioms EffectiveEncoding.candidateProductRowProgram_actions
#check EffectiveEncoding.candidateProductProgram_items
#print axioms EffectiveEncoding.candidateProductProgram_items
#check EffectiveEncoding.candidateProductProgram_actions
#print axioms EffectiveEncoding.candidateProductProgram_actions
#check EffectiveEncoding.candidateProduct_map
#print axioms EffectiveEncoding.candidateProduct_map
#check EffectiveEncoding.specSavedTriple_counts
#print axioms EffectiveEncoding.specSavedTriple_counts
#check EffectiveEncoding.specSavedTriple_prepared
#print axioms EffectiveEncoding.specSavedTriple_prepared
#check EffectiveEncoding.binaryTriplesProgram_candidates
#print axioms EffectiveEncoding.binaryTriplesProgram_candidates
#check EffectiveEncoding.binaryTriplesProgram_candidateLength
#print axioms EffectiveEncoding.binaryTriplesProgram_candidateLength
#check EffectiveEncoding.binaryTriplesProgram_filtered
#print axioms EffectiveEncoding.binaryTriplesProgram_filtered
#check EffectiveEncoding.binaryTriplesProgram_counts
#print axioms EffectiveEncoding.binaryTriplesProgram_counts
#check EffectiveEncoding.binaryTriplesProgram_prepared
#print axioms EffectiveEncoding.binaryTriplesProgram_prepared
#check EffectiveEncoding.binaryTriplesProgram_tests
#print axioms EffectiveEncoding.binaryTriplesProgram_tests
#check EffectiveEncoding.binaryTriplesProgram_testCount
#print axioms EffectiveEncoding.binaryTriplesProgram_testCount
#check EffectiveEncoding.binaryTriplesProgram_candidateWidth
#print axioms EffectiveEncoding.binaryTriplesProgram_candidateWidth
#check EffectiveEncoding.binaryTriplesProgram_predicateActions
#print axioms EffectiveEncoding.binaryTriplesProgram_predicateActions
#check EffectiveEncoding.binaryTriplesProgram_actions
#print axioms EffectiveEncoding.binaryTriplesProgram_actions
#check EffectiveEncoding.binaryTriplesProgram_actions_polynomial
#print axioms EffectiveEncoding.binaryTriplesProgram_actions_polynomial
#check EffectiveEncoding.binaryGeneratedRankProgram_scan
#print axioms EffectiveEncoding.binaryGeneratedRankProgram_scan
#check EffectiveEncoding.binaryGeneratedRankProgram_input
#print axioms EffectiveEncoding.binaryGeneratedRankProgram_input
#check EffectiveEncoding.binaryGeneratedRankProgram_index
#print axioms EffectiveEncoding.binaryGeneratedRankProgram_index
#check EffectiveEncoding.binaryGeneratedRankProgram_encoding
#print axioms EffectiveEncoding.binaryGeneratedRankProgram_encoding
#check EffectiveEncoding.binaryGeneratedRankProgram_output
#print axioms EffectiveEncoding.binaryGeneratedRankProgram_output
#check EffectiveEncoding.binaryGeneratedRankProgram_actions
#print axioms EffectiveEncoding.binaryGeneratedRankProgram_actions
#check EffectiveEncoding.binaryGeneratedRankProgram_actions_polynomial
#print axioms EffectiveEncoding.binaryGeneratedRankProgram_actions_polynomial
#check EffectiveEncoding.SavedCountWord
#print axioms EffectiveEncoding.SavedCountWord
#check EffectiveEncoding.savedCountSuccessor
#print axioms EffectiveEncoding.savedCountSuccessor
#check EffectiveEncoding.BinaryCountRangeResult
#print axioms EffectiveEncoding.BinaryCountRangeResult
#check EffectiveEncoding.binaryCountRangeProgram
#print axioms EffectiveEncoding.binaryCountRangeProgram
#check EffectiveEncoding.BinaryCountRangeResult.incrementTrimActions
#print axioms EffectiveEncoding.BinaryCountRangeResult.incrementTrimActions
#check EffectiveEncoding.BinaryCountRangeResult.actions
#print axioms EffectiveEncoding.BinaryCountRangeResult.actions
#check EffectiveEncoding.nativeOrderIsAtMost
#print axioms EffectiveEncoding.nativeOrderIsAtMost
#check EffectiveEncoding.BinaryTriplePredicateResult
#print axioms EffectiveEncoding.BinaryTriplePredicateResult
#check EffectiveEncoding.binaryTripleBoundProgram
#print axioms EffectiveEncoding.binaryTripleBoundProgram
#check EffectiveEncoding.BinaryTriplePredicateResult.actions
#print axioms EffectiveEncoding.BinaryTriplePredicateResult.actions
#check EffectiveEncoding.BinaryCandidateFilterResult
#print axioms EffectiveEncoding.BinaryCandidateFilterResult
#check EffectiveEncoding.binaryCandidateFilterProgram
#print axioms EffectiveEncoding.binaryCandidateFilterProgram
#check EffectiveEncoding.BinaryCandidateFilterResult.predicateActions
#print axioms EffectiveEncoding.BinaryCandidateFilterResult.predicateActions
#check EffectiveEncoding.CandidateProductTrace
#print axioms EffectiveEncoding.CandidateProductTrace
#check EffectiveEncoding.CandidateProductTrace.actions
#print axioms EffectiveEncoding.CandidateProductTrace.actions
#check EffectiveEncoding.CandidateProductResult
#print axioms EffectiveEncoding.CandidateProductResult
#check EffectiveEncoding.candidateProductRowProgram
#print axioms EffectiveEncoding.candidateProductRowProgram
#check EffectiveEncoding.candidateProductProgram
#print axioms EffectiveEncoding.candidateProductProgram
#check EffectiveEncoding.SavedTripleWords
#print axioms EffectiveEncoding.SavedTripleWords
#check EffectiveEncoding.savedTripleCounts
#print axioms EffectiveEncoding.savedTripleCounts
#check EffectiveEncoding.savedTriplePrepared
#print axioms EffectiveEncoding.savedTriplePrepared
#check EffectiveEncoding.specSavedTriple
#print axioms EffectiveEncoding.specSavedTriple
#check EffectiveEncoding.BinaryTriplesResult
#print axioms EffectiveEncoding.BinaryTriplesResult
#check EffectiveEncoding.binaryTriplesProgram
#print axioms EffectiveEncoding.binaryTriplesProgram
#check EffectiveEncoding.BinaryTriplesResult.actions
#print axioms EffectiveEncoding.BinaryTriplesResult.actions
#check EffectiveEncoding.BinaryGeneratedRankResult
#print axioms EffectiveEncoding.BinaryGeneratedRankResult
#check EffectiveEncoding.binaryGeneratedRankProgram
#print axioms EffectiveEncoding.binaryGeneratedRankProgram
#check EffectiveEncoding.BinaryGeneratedRankResult.actions
#print axioms EffectiveEncoding.BinaryGeneratedRankResult.actions
