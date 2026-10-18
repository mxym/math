import EffectiveEncoding.ProviderTrace

open Lean Elab Command
namespace EffectiveEncodingTraceVerification

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

end EffectiveEncodingTraceVerification

run_cmd (EffectiveEncodingTraceVerification.checkKinds [
  ``EffectiveEncoding.actualTargetCacheHeight_ge,
  ``EffectiveEncoding.actualTarget_PacketOracleHeight,
  ``EffectiveEncoding.actualGate_PacketOracleHeight,
  ``EffectiveEncoding.actualDescriptorTrace_integerBitBudget,
  ``EffectiveEncoding.actualDescriptorTraceBudget_polynomial,
  ``EffectiveEncoding.actualDescriptorTrace_polynomial,
  ``EffectiveEncoding.actualDescriptorTrace_subtreeBound,
  ``EffectiveEncoding.extractionCode_length_polynomial,
  ``EffectiveEncoding.extractionPrecision_polynomial,
  ``EffectiveEncoding.extraction_provider_subtree_polynomial,
  ``EffectiveEncoding.extraction_trace_subtree_polynomial
] [
  ``EffectiveEncoding.actualTargetCacheHeight,
  ``EffectiveEncoding.actualDescriptorTraceBudget,
  ``EffectiveEncoding.actualTraceConstant,
  ``EffectiveEncoding.actualGatePolynomial,
  ``EffectiveEncoding.pipelinePrecisionPolynomial,
  ``EffectiveEncoding.extractionOperandPolynomial
])

#check EffectiveEncoding.actualTargetCacheHeight_ge
#print axioms EffectiveEncoding.actualTargetCacheHeight_ge
#check EffectiveEncoding.actualTarget_PacketOracleHeight
#print axioms EffectiveEncoding.actualTarget_PacketOracleHeight
#check EffectiveEncoding.actualGate_PacketOracleHeight
#print axioms EffectiveEncoding.actualGate_PacketOracleHeight
#check EffectiveEncoding.actualDescriptorTrace_integerBitBudget
#print axioms EffectiveEncoding.actualDescriptorTrace_integerBitBudget
#check EffectiveEncoding.actualDescriptorTraceBudget_polynomial
#print axioms EffectiveEncoding.actualDescriptorTraceBudget_polynomial
#check EffectiveEncoding.actualDescriptorTrace_polynomial
#print axioms EffectiveEncoding.actualDescriptorTrace_polynomial
#check EffectiveEncoding.actualDescriptorTrace_subtreeBound
#print axioms EffectiveEncoding.actualDescriptorTrace_subtreeBound
#check EffectiveEncoding.extractionCode_length_polynomial
#print axioms EffectiveEncoding.extractionCode_length_polynomial
#check EffectiveEncoding.extractionPrecision_polynomial
#print axioms EffectiveEncoding.extractionPrecision_polynomial
#check EffectiveEncoding.extraction_provider_subtree_polynomial
#print axioms EffectiveEncoding.extraction_provider_subtree_polynomial
#check EffectiveEncoding.extraction_trace_subtree_polynomial
#print axioms EffectiveEncoding.extraction_trace_subtree_polynomial
#check EffectiveEncoding.actualTargetCacheHeight
#print axioms EffectiveEncoding.actualTargetCacheHeight
#check EffectiveEncoding.actualDescriptorTraceBudget
#print axioms EffectiveEncoding.actualDescriptorTraceBudget
#check EffectiveEncoding.actualTraceConstant
#print axioms EffectiveEncoding.actualTraceConstant
#check EffectiveEncoding.actualGatePolynomial
#print axioms EffectiveEncoding.actualGatePolynomial
#check EffectiveEncoding.pipelinePrecisionPolynomial
#print axioms EffectiveEncoding.pipelinePrecisionPolynomial
#check EffectiveEncoding.extractionOperandPolynomial
#print axioms EffectiveEncoding.extractionOperandPolynomial
