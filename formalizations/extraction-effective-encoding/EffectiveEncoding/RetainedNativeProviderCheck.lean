import EffectiveEncoding.FullyRetainedNativeExtraction
import EffectiveEncoding.RetainedNativeProviderEvaluation

open Lean Elab Command
namespace EffectiveEncodingRetainedNativeProviderVerification

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

end EffectiveEncodingRetainedNativeProviderVerification

run_cmd (EffectiveEncodingRetainedNativeProviderVerification.checkKinds [
  ``EffectiveEncoding.nativeProviderLiteral_refines,
  ``EffectiveEncoding.nativeProviderHalf_refines,
  ``EffectiveEncoding.nativeProviderMinusOne_refines,
  ``EffectiveEncoding.prepareNativeAtomInput_cos_refines,
  ``EffectiveEncoding.prepareNativeAtomInput_sin_refines,
  ``EffectiveEncoding.nativeInputHalfCos_refines,
  ``EffectiveEncoding.nativeInputHalfSin_refines,
  ``EffectiveEncoding.prepareNativeAngleInput_cos_refines,
  ``EffectiveEncoding.prepareNativeAngleInput_sin_refines,
  ``EffectiveEncoding.nativePhaseCosExpression_refines,
  ``EffectiveEncoding.nativePhaseSinExpression_refines,
  ``EffectiveEncoding.prepareNativeSingleInput_packet_refines,
  ``EffectiveEncoding.nativeProviderExpression_bitBudget,
  ``EffectiveEncoding.nativeProviderExpression_operations,
  ``EffectiveEncoding.nativeProviderQuery_algebra,
  ``EffectiveEncoding.nativeProviderPacketProgram_booleanActions,
  ``EffectiveEncoding.nativeProviderQueryCoefficient_polynomial,
  ``EffectiveEncoding.nativeProviderPacketProgram_booleanActions_kp,
  ``EffectiveEncoding.buildNativeTargetPrograms_values,
  ``EffectiveEncoding.retainedNativeTargetRun_erase,
  ``EffectiveEncoding.retainedNativeTargetRun_cache,
  ``EffectiveEncoding.retainedNativeTargetRun_providerActions_bound,
  ``EffectiveEncoding.nativeProviderCache_algebra,
  ``EffectiveEncoding.retainedNativeTargetRun_providerActions_polynomial,
  ``EffectiveEncoding.nativeProviderCacheCoefficient_polynomial,
  ``EffectiveEncoding.compileProviderGate_erase,
  ``EffectiveEncoding.compileProviderWord_erase,
  ``EffectiveEncoding.compileProviderWord_providerActions,
  ``EffectiveEncoding.fullyRetainedNativeRun_erase,
  ``EffectiveEncoding.fullyRetainedNativeRun_word,
  ``EffectiveEncoding.fullyRetainedNativeRun_providerActions,
  ``EffectiveEncoding.fullyRetainedNativeRun_preparationActions,
  ``EffectiveEncoding.fullyRetainedNativeRun_numericalActions,
  ``EffectiveEncoding.nativeAccountedPrimitive_algebra,
  ``EffectiveEncoding.fullyRetainedNativeRun_accountedPrimitiveActions,
  ``EffectiveEncoding.fullyRetainedNativeRun_fidelity
] [
  ``EffectiveEncoding.nativeProviderQueryCoefficient,
  ``EffectiveEncoding.buildNativeTargetPrograms,
  ``EffectiveEncoding.RetainedNativeTargetResult,
  ``EffectiveEncoding.retainedNativeTargetRun,
  ``EffectiveEncoding.RetainedNativeTargetResult.erase,
  ``EffectiveEncoding.RetainedNativeTargetResult.providerActions,
  ``EffectiveEncoding.nativeProviderCacheCoefficient,
  ``EffectiveEncoding.nativeProviderCachePolynomialConstant,
  ``EffectiveEncoding.ProviderCompiledLabelRun,
  ``EffectiveEncoding.ProviderCompiledLabelRun.erase,
  ``EffectiveEncoding.compileProviderGate,
  ``EffectiveEncoding.compileProviderWord,
  ``EffectiveEncoding.ProviderCompiledLabelRun.providerActions,
  ``EffectiveEncoding.FullyRetainedNativeResult,
  ``EffectiveEncoding.FullyRetainedNativeResult.erase,
  ``EffectiveEncoding.fullyRetainedNativeRun,
  ``EffectiveEncoding.FullyRetainedNativeResult.accountedPrimitiveActions
])

#check EffectiveEncoding.nativeProviderLiteral_refines
#print axioms EffectiveEncoding.nativeProviderLiteral_refines
#check EffectiveEncoding.nativeProviderHalf_refines
#print axioms EffectiveEncoding.nativeProviderHalf_refines
#check EffectiveEncoding.nativeProviderMinusOne_refines
#print axioms EffectiveEncoding.nativeProviderMinusOne_refines
#check EffectiveEncoding.prepareNativeAtomInput_cos_refines
#print axioms EffectiveEncoding.prepareNativeAtomInput_cos_refines
#check EffectiveEncoding.prepareNativeAtomInput_sin_refines
#print axioms EffectiveEncoding.prepareNativeAtomInput_sin_refines
#check EffectiveEncoding.nativeInputHalfCos_refines
#print axioms EffectiveEncoding.nativeInputHalfCos_refines
#check EffectiveEncoding.nativeInputHalfSin_refines
#print axioms EffectiveEncoding.nativeInputHalfSin_refines
#check EffectiveEncoding.prepareNativeAngleInput_cos_refines
#print axioms EffectiveEncoding.prepareNativeAngleInput_cos_refines
#check EffectiveEncoding.prepareNativeAngleInput_sin_refines
#print axioms EffectiveEncoding.prepareNativeAngleInput_sin_refines
#check EffectiveEncoding.nativePhaseCosExpression_refines
#print axioms EffectiveEncoding.nativePhaseCosExpression_refines
#check EffectiveEncoding.nativePhaseSinExpression_refines
#print axioms EffectiveEncoding.nativePhaseSinExpression_refines
#check EffectiveEncoding.prepareNativeSingleInput_packet_refines
#print axioms EffectiveEncoding.prepareNativeSingleInput_packet_refines
#check EffectiveEncoding.nativeProviderExpression_bitBudget
#print axioms EffectiveEncoding.nativeProviderExpression_bitBudget
#check EffectiveEncoding.nativeProviderExpression_operations
#print axioms EffectiveEncoding.nativeProviderExpression_operations
#check EffectiveEncoding.nativeProviderQuery_algebra
#print axioms EffectiveEncoding.nativeProviderQuery_algebra
#check EffectiveEncoding.nativeProviderPacketProgram_booleanActions
#print axioms EffectiveEncoding.nativeProviderPacketProgram_booleanActions
#check EffectiveEncoding.nativeProviderQueryCoefficient_polynomial
#print axioms EffectiveEncoding.nativeProviderQueryCoefficient_polynomial
#check EffectiveEncoding.nativeProviderPacketProgram_booleanActions_kp
#print axioms EffectiveEncoding.nativeProviderPacketProgram_booleanActions_kp
#check EffectiveEncoding.buildNativeTargetPrograms_values
#print axioms EffectiveEncoding.buildNativeTargetPrograms_values
#check EffectiveEncoding.retainedNativeTargetRun_erase
#print axioms EffectiveEncoding.retainedNativeTargetRun_erase
#check EffectiveEncoding.retainedNativeTargetRun_cache
#print axioms EffectiveEncoding.retainedNativeTargetRun_cache
#check EffectiveEncoding.retainedNativeTargetRun_providerActions_bound
#print axioms EffectiveEncoding.retainedNativeTargetRun_providerActions_bound
#check EffectiveEncoding.nativeProviderCache_algebra
#print axioms EffectiveEncoding.nativeProviderCache_algebra
#check EffectiveEncoding.retainedNativeTargetRun_providerActions_polynomial
#print axioms EffectiveEncoding.retainedNativeTargetRun_providerActions_polynomial
#check EffectiveEncoding.nativeProviderCacheCoefficient_polynomial
#print axioms EffectiveEncoding.nativeProviderCacheCoefficient_polynomial
#check EffectiveEncoding.compileProviderGate_erase
#print axioms EffectiveEncoding.compileProviderGate_erase
#check EffectiveEncoding.compileProviderWord_erase
#print axioms EffectiveEncoding.compileProviderWord_erase
#check EffectiveEncoding.compileProviderWord_providerActions
#print axioms EffectiveEncoding.compileProviderWord_providerActions
#check EffectiveEncoding.fullyRetainedNativeRun_erase
#print axioms EffectiveEncoding.fullyRetainedNativeRun_erase
#check EffectiveEncoding.fullyRetainedNativeRun_word
#print axioms EffectiveEncoding.fullyRetainedNativeRun_word
#check EffectiveEncoding.fullyRetainedNativeRun_providerActions
#print axioms EffectiveEncoding.fullyRetainedNativeRun_providerActions
#check EffectiveEncoding.fullyRetainedNativeRun_preparationActions
#print axioms EffectiveEncoding.fullyRetainedNativeRun_preparationActions
#check EffectiveEncoding.fullyRetainedNativeRun_numericalActions
#print axioms EffectiveEncoding.fullyRetainedNativeRun_numericalActions
#check EffectiveEncoding.nativeAccountedPrimitive_algebra
#print axioms EffectiveEncoding.nativeAccountedPrimitive_algebra
#check EffectiveEncoding.fullyRetainedNativeRun_accountedPrimitiveActions
#print axioms EffectiveEncoding.fullyRetainedNativeRun_accountedPrimitiveActions
#check EffectiveEncoding.fullyRetainedNativeRun_fidelity
#print axioms EffectiveEncoding.fullyRetainedNativeRun_fidelity
#check EffectiveEncoding.nativeProviderQueryCoefficient
#print axioms EffectiveEncoding.nativeProviderQueryCoefficient
#check EffectiveEncoding.buildNativeTargetPrograms
#print axioms EffectiveEncoding.buildNativeTargetPrograms
#check EffectiveEncoding.RetainedNativeTargetResult
#print axioms EffectiveEncoding.RetainedNativeTargetResult
#check EffectiveEncoding.retainedNativeTargetRun
#print axioms EffectiveEncoding.retainedNativeTargetRun
#check EffectiveEncoding.RetainedNativeTargetResult.erase
#print axioms EffectiveEncoding.RetainedNativeTargetResult.erase
#check EffectiveEncoding.RetainedNativeTargetResult.providerActions
#print axioms EffectiveEncoding.RetainedNativeTargetResult.providerActions
#check EffectiveEncoding.nativeProviderCacheCoefficient
#print axioms EffectiveEncoding.nativeProviderCacheCoefficient
#check EffectiveEncoding.nativeProviderCachePolynomialConstant
#print axioms EffectiveEncoding.nativeProviderCachePolynomialConstant
#check EffectiveEncoding.ProviderCompiledLabelRun
#print axioms EffectiveEncoding.ProviderCompiledLabelRun
#check EffectiveEncoding.ProviderCompiledLabelRun.erase
#print axioms EffectiveEncoding.ProviderCompiledLabelRun.erase
#check EffectiveEncoding.compileProviderGate
#print axioms EffectiveEncoding.compileProviderGate
#check EffectiveEncoding.compileProviderWord
#print axioms EffectiveEncoding.compileProviderWord
#check EffectiveEncoding.ProviderCompiledLabelRun.providerActions
#print axioms EffectiveEncoding.ProviderCompiledLabelRun.providerActions
#check EffectiveEncoding.FullyRetainedNativeResult
#print axioms EffectiveEncoding.FullyRetainedNativeResult
#check EffectiveEncoding.FullyRetainedNativeResult.erase
#print axioms EffectiveEncoding.FullyRetainedNativeResult.erase
#check EffectiveEncoding.fullyRetainedNativeRun
#print axioms EffectiveEncoding.fullyRetainedNativeRun
#check EffectiveEncoding.FullyRetainedNativeResult.accountedPrimitiveActions
#print axioms EffectiveEncoding.FullyRetainedNativeResult.accountedPrimitiveActions
