import EffectiveEncoding.CandidateSerializedPolynomial
import EffectiveEncoding.CandidateTerminalEvaluation

open Lean Elab Command
namespace EffectiveEncodingCandidateTerminalVerification

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

end EffectiveEncodingCandidateTerminalVerification

run_cmd (EffectiveEncodingCandidateTerminalVerification.checkKinds [
  ``EffectiveEncoding.candidateSerializedRun_generation,
  ``EffectiveEncoding.candidateSerializedRun_precision,
  ``EffectiveEncoding.candidateSerializedRun_suffix_roundtrip,
  ``EffectiveEncoding.candidateSerializedRun_roundtrip,
  ``EffectiveEncoding.candidateSerializedRun_word,
  ``EffectiveEncoding.candidateSerializedRun_decoded_word,
  ``EffectiveEncoding.candidateSerializedRun_fidelity,
  ``EffectiveEncoding.RetainedAssembledTargetResult.primitiveActions_eq,
  ``EffectiveEncoding.retainedAssembledTargetRun_primitiveActions,
  ``EffectiveEncoding.candidateSerializedRun_targetActions,
  ``EffectiveEncoding.candidateSerializedRun_outputLength,
  ``EffectiveEncoding.candidateSerializedRun_outerActions,
  ``EffectiveEncoding.candidateSerializedRun_streamLength,
  ``EffectiveEncoding.candidateSerializedRun_streamActions,
  ``EffectiveEncoding.candidateSerializedRun_accountedPrimitiveActions,
  ``EffectiveEncoding.candidateBudget_add_algebra,
  ``EffectiveEncoding.candidateSerializedPrimitiveBudget_enlarge,
  ``EffectiveEncoding.candidateGeneration_uniform,
  ``EffectiveEncoding.candidateSerializedPrimitiveBudget_polynomial,
  ``EffectiveEncoding.candidateSerializedRun_accountedPrimitiveActions_polynomial
] [
  ``EffectiveEncoding.CandidateSerializedResult,
  ``EffectiveEncoding.candidateSerializedRun,
  ``EffectiveEncoding.CandidateSerializedResult.decoded,
  ``EffectiveEncoding.RetainedAssembledTargetResult.primitiveActions,
  ``EffectiveEncoding.CandidateSerializedResult.targetActions,
  ``EffectiveEncoding.CandidateSerializedResult.accountedPrimitiveActions,
  ``EffectiveEncoding.candidateSerializedPrimitiveBudget,
  ``EffectiveEncoding.candidateSerializedPolynomialConstant
])

#check EffectiveEncoding.candidateSerializedRun_generation
#print axioms EffectiveEncoding.candidateSerializedRun_generation
#check EffectiveEncoding.candidateSerializedRun_precision
#print axioms EffectiveEncoding.candidateSerializedRun_precision
#check EffectiveEncoding.candidateSerializedRun_suffix_roundtrip
#print axioms EffectiveEncoding.candidateSerializedRun_suffix_roundtrip
#check EffectiveEncoding.candidateSerializedRun_roundtrip
#print axioms EffectiveEncoding.candidateSerializedRun_roundtrip
#check EffectiveEncoding.candidateSerializedRun_word
#print axioms EffectiveEncoding.candidateSerializedRun_word
#check EffectiveEncoding.candidateSerializedRun_decoded_word
#print axioms EffectiveEncoding.candidateSerializedRun_decoded_word
#check EffectiveEncoding.candidateSerializedRun_fidelity
#print axioms EffectiveEncoding.candidateSerializedRun_fidelity
#check EffectiveEncoding.RetainedAssembledTargetResult.primitiveActions_eq
#print axioms EffectiveEncoding.RetainedAssembledTargetResult.primitiveActions_eq
#check EffectiveEncoding.retainedAssembledTargetRun_primitiveActions
#print axioms EffectiveEncoding.retainedAssembledTargetRun_primitiveActions
#check EffectiveEncoding.candidateSerializedRun_targetActions
#print axioms EffectiveEncoding.candidateSerializedRun_targetActions
#check EffectiveEncoding.candidateSerializedRun_outputLength
#print axioms EffectiveEncoding.candidateSerializedRun_outputLength
#check EffectiveEncoding.candidateSerializedRun_outerActions
#print axioms EffectiveEncoding.candidateSerializedRun_outerActions
#check EffectiveEncoding.candidateSerializedRun_streamLength
#print axioms EffectiveEncoding.candidateSerializedRun_streamLength
#check EffectiveEncoding.candidateSerializedRun_streamActions
#print axioms EffectiveEncoding.candidateSerializedRun_streamActions
#check EffectiveEncoding.candidateSerializedRun_accountedPrimitiveActions
#print axioms EffectiveEncoding.candidateSerializedRun_accountedPrimitiveActions
#check EffectiveEncoding.candidateBudget_add_algebra
#print axioms EffectiveEncoding.candidateBudget_add_algebra
#check EffectiveEncoding.candidateSerializedPrimitiveBudget_enlarge
#print axioms EffectiveEncoding.candidateSerializedPrimitiveBudget_enlarge
#check EffectiveEncoding.candidateGeneration_uniform
#print axioms EffectiveEncoding.candidateGeneration_uniform
#check EffectiveEncoding.candidateSerializedPrimitiveBudget_polynomial
#print axioms EffectiveEncoding.candidateSerializedPrimitiveBudget_polynomial
#check EffectiveEncoding.candidateSerializedRun_accountedPrimitiveActions_polynomial
#print axioms EffectiveEncoding.candidateSerializedRun_accountedPrimitiveActions_polynomial
#check EffectiveEncoding.CandidateSerializedResult
#print axioms EffectiveEncoding.CandidateSerializedResult
#check EffectiveEncoding.candidateSerializedRun
#print axioms EffectiveEncoding.candidateSerializedRun
#check EffectiveEncoding.CandidateSerializedResult.decoded
#print axioms EffectiveEncoding.CandidateSerializedResult.decoded
#check EffectiveEncoding.RetainedAssembledTargetResult.primitiveActions
#print axioms EffectiveEncoding.RetainedAssembledTargetResult.primitiveActions
#check EffectiveEncoding.CandidateSerializedResult.targetActions
#print axioms EffectiveEncoding.CandidateSerializedResult.targetActions
#check EffectiveEncoding.CandidateSerializedResult.accountedPrimitiveActions
#print axioms EffectiveEncoding.CandidateSerializedResult.accountedPrimitiveActions
#check EffectiveEncoding.candidateSerializedPrimitiveBudget
#print axioms EffectiveEncoding.candidateSerializedPrimitiveBudget
#check EffectiveEncoding.candidateSerializedPolynomialConstant
#print axioms EffectiveEncoding.candidateSerializedPolynomialConstant
