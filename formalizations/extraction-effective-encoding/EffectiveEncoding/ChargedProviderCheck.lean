import EffectiveEncoding.ChargedProviderCompiler

open Lean Elab Command
namespace EffectiveEncodingChargedProviderVerification

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

end EffectiveEncodingChargedProviderVerification

run_cmd (EffectiveEncodingChargedProviderVerification.checkKinds [
  ``EffectiveEncoding.AngleAtom.rawCosExpression_run,
  ``EffectiveEncoding.AngleAtom.rawSinExpression_run,
  ``EffectiveEncoding.AngleCode.rawCosExpression_run,
  ``EffectiveEncoding.AngleCode.rawSinExpression_run,
  ``EffectiveEncoding.rawPhaseCosExpression_run,
  ``EffectiveEncoding.rawPhaseSinExpression_run,
  ``EffectiveEncoding.SingleCode.rawPacketExpression_run,
  ``EffectiveEncoding.SingleCode.rawPacketProgram_value,
  ``EffectiveEncoding.integerFraction_height,
  ``EffectiveEncoding.AngleAtom.rawExpression_operations,
  ``EffectiveEncoding.AngleCode.rawExpression_operations,
  ``EffectiveEncoding.SingleCode.rawPacketExpression_operations,
  ``EffectiveEncoding.AngleAtom.rawExpression_budget,
  ``EffectiveEncoding.AngleCode.rawExpression_budget,
  ``EffectiveEncoding.SingleCode.rawPacketExpression_budget,
  ``EffectiveEncoding.rawProviderHeightBudget_le,
  ``EffectiveEncoding.extractionCode_rawProviderExpression_budget,
  ``EffectiveEncoding.extractionCode_rawProviderExpression_operations,
  ``EffectiveEncoding.extractionCode_rawPacketProgram_rootCharge,
  ``EffectiveEncoding.extractionCode_rawProviderExpression_subtreeBound,
  ``EffectiveEncoding.rawProviderBinaryExponent,
  ``EffectiveEncoding.extractionCode_rawProviderExpression_binaryProgramOperandTrace_height,
  ``EffectiveEncoding.rawProviderRootBudget_mono,
  ``EffectiveEncoding.rawTargetProgramCacheCharge_bound,
  ``EffectiveEncoding.rawProviderCacheRoot_algebra,
  ``EffectiveEncoding.rawTargetProgramCacheCharge_polynomial,
  ``EffectiveEncoding.rawProviderCoefficient_algebra,
  ``EffectiveEncoding.rawProviderCacheRootCoefficient_polynomial,
  ``EffectiveEncoding.rawTargetProgramCacheCharge_polynomial_kq,
  ``EffectiveEncoding.rawTargetProgramCache_values,
  ``EffectiveEncoding.targetProgramDescriptorRun_result,
  ``EffectiveEncoding.targetProgramDescriptorRun_rootCharge,
  ``EffectiveEncoding.targetProgramDescriptorRun_rootCharge_bound,
  ``EffectiveEncoding.chargedProviderExtractionCode_eq,
  ``EffectiveEncoding.chargedProviderExtractionCode_fidelity,
  ``EffectiveEncoding.extractionProviderProgramRootCharge_bound
] [
  ``EffectiveEncoding.AngleAtom.rawCosExpression,
  ``EffectiveEncoding.AngleAtom.rawSinExpression,
  ``EffectiveEncoding.AngleCode.rawCosExpression,
  ``EffectiveEncoding.AngleCode.rawSinExpression,
  ``EffectiveEncoding.rawPhaseCosExpression,
  ``EffectiveEncoding.rawPhaseSinExpression,
  ``EffectiveEncoding.SingleCode.rawPacketExpression,
  ``EffectiveEncoding.SingleCode.rawPacketProgram,
  ``EffectiveEncoding.rawProviderHeightBudget,
  ``EffectiveEncoding.rawTargetProgramCacheCharge,
  ``EffectiveEncoding.rawProviderRootBudget,
  ``EffectiveEncoding.rawProviderCacheRootCoefficient,
  ``EffectiveEncoding.rawProviderCachePolynomialConstant,
  ``EffectiveEncoding.rawTargetProgramCache,
  ``EffectiveEncoding.targetProgramDescriptorRun,
  ``EffectiveEncoding.chargedProviderExtractionCode,
  ``EffectiveEncoding.gateProviderProgramRootCharge,
  ``EffectiveEncoding.extractionProviderProgramRootCharge
])

#check EffectiveEncoding.AngleAtom.rawCosExpression_run
#print axioms EffectiveEncoding.AngleAtom.rawCosExpression_run
#check EffectiveEncoding.AngleAtom.rawSinExpression_run
#print axioms EffectiveEncoding.AngleAtom.rawSinExpression_run
#check EffectiveEncoding.AngleCode.rawCosExpression_run
#print axioms EffectiveEncoding.AngleCode.rawCosExpression_run
#check EffectiveEncoding.AngleCode.rawSinExpression_run
#print axioms EffectiveEncoding.AngleCode.rawSinExpression_run
#check EffectiveEncoding.rawPhaseCosExpression_run
#print axioms EffectiveEncoding.rawPhaseCosExpression_run
#check EffectiveEncoding.rawPhaseSinExpression_run
#print axioms EffectiveEncoding.rawPhaseSinExpression_run
#check EffectiveEncoding.SingleCode.rawPacketExpression_run
#print axioms EffectiveEncoding.SingleCode.rawPacketExpression_run
#check EffectiveEncoding.SingleCode.rawPacketProgram_value
#print axioms EffectiveEncoding.SingleCode.rawPacketProgram_value
#check EffectiveEncoding.integerFraction_height
#print axioms EffectiveEncoding.integerFraction_height
#check EffectiveEncoding.AngleAtom.rawExpression_operations
#print axioms EffectiveEncoding.AngleAtom.rawExpression_operations
#check EffectiveEncoding.AngleCode.rawExpression_operations
#print axioms EffectiveEncoding.AngleCode.rawExpression_operations
#check EffectiveEncoding.SingleCode.rawPacketExpression_operations
#print axioms EffectiveEncoding.SingleCode.rawPacketExpression_operations
#check EffectiveEncoding.AngleAtom.rawExpression_budget
#print axioms EffectiveEncoding.AngleAtom.rawExpression_budget
#check EffectiveEncoding.AngleCode.rawExpression_budget
#print axioms EffectiveEncoding.AngleCode.rawExpression_budget
#check EffectiveEncoding.SingleCode.rawPacketExpression_budget
#print axioms EffectiveEncoding.SingleCode.rawPacketExpression_budget
#check EffectiveEncoding.rawProviderHeightBudget_le
#print axioms EffectiveEncoding.rawProviderHeightBudget_le
#check EffectiveEncoding.extractionCode_rawProviderExpression_budget
#print axioms EffectiveEncoding.extractionCode_rawProviderExpression_budget
#check EffectiveEncoding.extractionCode_rawProviderExpression_operations
#print axioms EffectiveEncoding.extractionCode_rawProviderExpression_operations
#check EffectiveEncoding.extractionCode_rawPacketProgram_rootCharge
#print axioms EffectiveEncoding.extractionCode_rawPacketProgram_rootCharge
#check EffectiveEncoding.extractionCode_rawProviderExpression_subtreeBound
#print axioms EffectiveEncoding.extractionCode_rawProviderExpression_subtreeBound
#check EffectiveEncoding.rawProviderBinaryExponent
#print axioms EffectiveEncoding.rawProviderBinaryExponent
#check EffectiveEncoding.extractionCode_rawProviderExpression_binaryProgramOperandTrace_height
#print axioms EffectiveEncoding.extractionCode_rawProviderExpression_binaryProgramOperandTrace_height
#check EffectiveEncoding.rawProviderRootBudget_mono
#print axioms EffectiveEncoding.rawProviderRootBudget_mono
#check EffectiveEncoding.rawTargetProgramCacheCharge_bound
#print axioms EffectiveEncoding.rawTargetProgramCacheCharge_bound
#check EffectiveEncoding.rawProviderCacheRoot_algebra
#print axioms EffectiveEncoding.rawProviderCacheRoot_algebra
#check EffectiveEncoding.rawTargetProgramCacheCharge_polynomial
#print axioms EffectiveEncoding.rawTargetProgramCacheCharge_polynomial
#check EffectiveEncoding.rawProviderCoefficient_algebra
#print axioms EffectiveEncoding.rawProviderCoefficient_algebra
#check EffectiveEncoding.rawProviderCacheRootCoefficient_polynomial
#print axioms EffectiveEncoding.rawProviderCacheRootCoefficient_polynomial
#check EffectiveEncoding.rawTargetProgramCacheCharge_polynomial_kq
#print axioms EffectiveEncoding.rawTargetProgramCacheCharge_polynomial_kq
#check EffectiveEncoding.rawTargetProgramCache_values
#print axioms EffectiveEncoding.rawTargetProgramCache_values
#check EffectiveEncoding.targetProgramDescriptorRun_result
#print axioms EffectiveEncoding.targetProgramDescriptorRun_result
#check EffectiveEncoding.targetProgramDescriptorRun_rootCharge
#print axioms EffectiveEncoding.targetProgramDescriptorRun_rootCharge
#check EffectiveEncoding.targetProgramDescriptorRun_rootCharge_bound
#print axioms EffectiveEncoding.targetProgramDescriptorRun_rootCharge_bound
#check EffectiveEncoding.chargedProviderExtractionCode_eq
#print axioms EffectiveEncoding.chargedProviderExtractionCode_eq
#check EffectiveEncoding.chargedProviderExtractionCode_fidelity
#print axioms EffectiveEncoding.chargedProviderExtractionCode_fidelity
#check EffectiveEncoding.extractionProviderProgramRootCharge_bound
#print axioms EffectiveEncoding.extractionProviderProgramRootCharge_bound
#check EffectiveEncoding.AngleAtom.rawCosExpression
#print axioms EffectiveEncoding.AngleAtom.rawCosExpression
#check EffectiveEncoding.AngleAtom.rawSinExpression
#print axioms EffectiveEncoding.AngleAtom.rawSinExpression
#check EffectiveEncoding.AngleCode.rawCosExpression
#print axioms EffectiveEncoding.AngleCode.rawCosExpression
#check EffectiveEncoding.AngleCode.rawSinExpression
#print axioms EffectiveEncoding.AngleCode.rawSinExpression
#check EffectiveEncoding.rawPhaseCosExpression
#print axioms EffectiveEncoding.rawPhaseCosExpression
#check EffectiveEncoding.rawPhaseSinExpression
#print axioms EffectiveEncoding.rawPhaseSinExpression
#check EffectiveEncoding.SingleCode.rawPacketExpression
#print axioms EffectiveEncoding.SingleCode.rawPacketExpression
#check EffectiveEncoding.SingleCode.rawPacketProgram
#print axioms EffectiveEncoding.SingleCode.rawPacketProgram
#check EffectiveEncoding.rawProviderHeightBudget
#print axioms EffectiveEncoding.rawProviderHeightBudget
#check EffectiveEncoding.rawTargetProgramCacheCharge
#print axioms EffectiveEncoding.rawTargetProgramCacheCharge
#check EffectiveEncoding.rawProviderRootBudget
#print axioms EffectiveEncoding.rawProviderRootBudget
#check EffectiveEncoding.rawProviderCacheRootCoefficient
#print axioms EffectiveEncoding.rawProviderCacheRootCoefficient
#check EffectiveEncoding.rawProviderCachePolynomialConstant
#print axioms EffectiveEncoding.rawProviderCachePolynomialConstant
#check EffectiveEncoding.rawTargetProgramCache
#print axioms EffectiveEncoding.rawTargetProgramCache
#check EffectiveEncoding.targetProgramDescriptorRun
#print axioms EffectiveEncoding.targetProgramDescriptorRun
#check EffectiveEncoding.chargedProviderExtractionCode
#print axioms EffectiveEncoding.chargedProviderExtractionCode
#check EffectiveEncoding.gateProviderProgramRootCharge
#print axioms EffectiveEncoding.gateProviderProgramRootCharge
#check EffectiveEncoding.extractionProviderProgramRootCharge
#print axioms EffectiveEncoding.extractionProviderProgramRootCharge
