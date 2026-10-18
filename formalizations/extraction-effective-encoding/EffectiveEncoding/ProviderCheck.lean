import EffectiveEncoding.ProviderTerminal
import Lean

open Lean Elab Command
namespace EffectiveEncodingProviderVerification

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

end EffectiveEncodingProviderVerification

run_cmd (EffectiveEncodingProviderVerification.checkKinds [
  ``EffectiveEncoding.meanPlusExpression_eval,
  ``EffectiveEncoding.halfCosExpression_eval,
  ``EffectiveEncoding.halfSinExpression_eval,
  ``EffectiveEncoding.AngleAtom.cosExpression_eval,
  ``EffectiveEncoding.AngleAtom.sinExpression_eval,
  ``EffectiveEncoding.AngleCode.cosExpression_eval,
  ``EffectiveEncoding.AngleCode.sinExpression_eval,
  ``EffectiveEncoding.phaseCosExpression_eval,
  ``EffectiveEncoding.phaseSinExpression_eval,
  ``EffectiveEncoding.SingleCode.packetExpression_eval,
  ``EffectiveEncoding.SingleCode.integerPacket_value,
  ``EffectiveEncoding.halfCosExpression_operations,
  ``EffectiveEncoding.halfSinExpression_operations,
  ``EffectiveEncoding.AngleAtom.expression_operations,
  ``EffectiveEncoding.AngleCode.expression_operations,
  ``EffectiveEncoding.SingleCode.packetExpression_operations,
  ``EffectiveEncoding.ratioLiteral_budget,
  ``EffectiveEncoding.AngleAtom.expression_budget,
  ``EffectiveEncoding.halfExpressionBudget_mono,
  ``EffectiveEncoding.halfExpressionBudget_ge,
  ``EffectiveEncoding.halfCosExpression_budget,
  ``EffectiveEncoding.halfSinExpression_budget,
  ``EffectiveEncoding.AngleCode.expression_budget,
  ``EffectiveEncoding.SingleCode.packetExpression_budget,
  ``EffectiveEncoding.SingleCode.integerPacket_height,
  ``EffectiveEncoding.extractionCode_provider_resources,
  ``EffectiveEncoding.fourMax_le,
  ``EffectiveEncoding.halfCosExpression_precision,
  ``EffectiveEncoding.halfSinExpression_precision,
  ``EffectiveEncoding.AngleAtom.expression_precision,
  ``EffectiveEncoding.AngleCode.expression_precision,
  ``EffectiveEncoding.SingleCode.packetExpression_precision,
  ``EffectiveEncoding.halvingBudget_power,
  ``EffectiveEncoding.binaryWidth_le,
  ``EffectiveEncoding.providerHeightBudget_polynomial,
  ``EffectiveEncoding.extractionCode_provider_precision,
  ``EffectiveEncoding.extractionCode_provider_integerHeight,
  ``EffectiveEncoding.extractionCode_targetCache_operations,
  ``EffectiveEncoding.extractionCode_targetCache_precision,
  ``EffectiveEncoding.extractionCode_targetCache_height,
  ``EffectiveEncoding.extractionTargetCacheOperations_bound,
  ``EffectiveEncoding.scalarIntermediateHeights_of_budget,
  ``EffectiveEncoding.packetIntermediateHeights_of_budget,
  ``EffectiveEncoding.SingleCode.packetExpression_intermediateHeights,
  ``EffectiveEncoding.extractionCode_provider_intermediateHeights,
  ``EffectiveEncoding.extractionCode_targetCache_intermediateHeights,
  ``EffectiveEncoding.integerRoot_work_operand_bound,
  ``EffectiveEncoding.integerTargetCache_values,
  ``EffectiveEncoding.integerDescriptorSynthesis_eq,
  ``EffectiveEncoding.integerNumericalExtractionCode_eq,
  ``EffectiveEncoding.integerNumericalExtractionCode_error,
  ``EffectiveEncoding.integerNumericalExtractionCode_fidelity,
  ``EffectiveEncoding.integerPacketBits_bound,
  ``EffectiveEncoding.extractionCode_integerTargetCacheBits,
  ``EffectiveEncoding.extractionWithTargetOperations_bound,
  ``EffectiveEncoding.extractionCode_provider_BitEnvelope,
  ``EffectiveEncoding.packetLiteral_budget_of_height,
  ``EffectiveEncoding.extractionCode_cachedTarget_BitEnvelope,
  ``EffectiveEncoding.extractionCode_actualCachedTarget_BitEnvelope
] [
  ``EffectiveEncoding.constantExpression,
  ``EffectiveEncoding.meanPlusExpression,
  ``EffectiveEncoding.halfCosExpression,
  ``EffectiveEncoding.halfSinExpression,
  ``EffectiveEncoding.AngleAtom.cosExpression,
  ``EffectiveEncoding.AngleAtom.sinExpression,
  ``EffectiveEncoding.AngleCode.cosExpression,
  ``EffectiveEncoding.AngleCode.sinExpression,
  ``EffectiveEncoding.phaseCosExpression,
  ``EffectiveEncoding.phaseSinExpression,
  ``EffectiveEncoding.SingleCode.packetExpression,
  ``EffectiveEncoding.SingleCode.integerPacket,
  ``EffectiveEncoding.halfExpressionBudget,
  ``EffectiveEncoding.providerHeightBudget,
  ``EffectiveEncoding.fourMax,
  ``EffectiveEncoding.scalarRootPrecision,
  ``EffectiveEncoding.packetRootPrecision,
  ``EffectiveEncoding.targetCacheOperations,
  ``EffectiveEncoding.gateTargetCacheOperations,
  ``EffectiveEncoding.extractionTargetCacheOperations,
  ``EffectiveEncoding.scalarIntermediateHeights,
  ``EffectiveEncoding.packetIntermediateHeights,
  ``EffectiveEncoding.integerTargetCache,
  ``EffectiveEncoding.integerDescriptorSynthesis,
  ``EffectiveEncoding.integerNumericalExtractionCode,
  ``EffectiveEncoding.integerPacketBits,
  ``EffectiveEncoding.integerTargetCacheBits,
  ``EffectiveEncoding.extractionWithTargetOperations
])

#check EffectiveEncoding.meanPlusExpression_eval
#print axioms EffectiveEncoding.meanPlusExpression_eval
#check EffectiveEncoding.halfCosExpression_eval
#print axioms EffectiveEncoding.halfCosExpression_eval
#check EffectiveEncoding.halfSinExpression_eval
#print axioms EffectiveEncoding.halfSinExpression_eval
#check EffectiveEncoding.AngleAtom.cosExpression_eval
#print axioms EffectiveEncoding.AngleAtom.cosExpression_eval
#check EffectiveEncoding.AngleAtom.sinExpression_eval
#print axioms EffectiveEncoding.AngleAtom.sinExpression_eval
#check EffectiveEncoding.AngleCode.cosExpression_eval
#print axioms EffectiveEncoding.AngleCode.cosExpression_eval
#check EffectiveEncoding.AngleCode.sinExpression_eval
#print axioms EffectiveEncoding.AngleCode.sinExpression_eval
#check EffectiveEncoding.phaseCosExpression_eval
#print axioms EffectiveEncoding.phaseCosExpression_eval
#check EffectiveEncoding.phaseSinExpression_eval
#print axioms EffectiveEncoding.phaseSinExpression_eval
#check EffectiveEncoding.SingleCode.packetExpression_eval
#print axioms EffectiveEncoding.SingleCode.packetExpression_eval
#check EffectiveEncoding.SingleCode.integerPacket_value
#print axioms EffectiveEncoding.SingleCode.integerPacket_value
#check EffectiveEncoding.halfCosExpression_operations
#print axioms EffectiveEncoding.halfCosExpression_operations
#check EffectiveEncoding.halfSinExpression_operations
#print axioms EffectiveEncoding.halfSinExpression_operations
#check EffectiveEncoding.AngleAtom.expression_operations
#print axioms EffectiveEncoding.AngleAtom.expression_operations
#check EffectiveEncoding.AngleCode.expression_operations
#print axioms EffectiveEncoding.AngleCode.expression_operations
#check EffectiveEncoding.SingleCode.packetExpression_operations
#print axioms EffectiveEncoding.SingleCode.packetExpression_operations
#check EffectiveEncoding.ratioLiteral_budget
#print axioms EffectiveEncoding.ratioLiteral_budget
#check EffectiveEncoding.AngleAtom.expression_budget
#print axioms EffectiveEncoding.AngleAtom.expression_budget
#check EffectiveEncoding.halfExpressionBudget_mono
#print axioms EffectiveEncoding.halfExpressionBudget_mono
#check EffectiveEncoding.halfExpressionBudget_ge
#print axioms EffectiveEncoding.halfExpressionBudget_ge
#check EffectiveEncoding.halfCosExpression_budget
#print axioms EffectiveEncoding.halfCosExpression_budget
#check EffectiveEncoding.halfSinExpression_budget
#print axioms EffectiveEncoding.halfSinExpression_budget
#check EffectiveEncoding.AngleCode.expression_budget
#print axioms EffectiveEncoding.AngleCode.expression_budget
#check EffectiveEncoding.SingleCode.packetExpression_budget
#print axioms EffectiveEncoding.SingleCode.packetExpression_budget
#check EffectiveEncoding.SingleCode.integerPacket_height
#print axioms EffectiveEncoding.SingleCode.integerPacket_height
#check EffectiveEncoding.extractionCode_provider_resources
#print axioms EffectiveEncoding.extractionCode_provider_resources
#check EffectiveEncoding.fourMax_le
#print axioms EffectiveEncoding.fourMax_le
#check EffectiveEncoding.halfCosExpression_precision
#print axioms EffectiveEncoding.halfCosExpression_precision
#check EffectiveEncoding.halfSinExpression_precision
#print axioms EffectiveEncoding.halfSinExpression_precision
#check EffectiveEncoding.AngleAtom.expression_precision
#print axioms EffectiveEncoding.AngleAtom.expression_precision
#check EffectiveEncoding.AngleCode.expression_precision
#print axioms EffectiveEncoding.AngleCode.expression_precision
#check EffectiveEncoding.SingleCode.packetExpression_precision
#print axioms EffectiveEncoding.SingleCode.packetExpression_precision
#check EffectiveEncoding.halvingBudget_power
#print axioms EffectiveEncoding.halvingBudget_power
#check EffectiveEncoding.binaryWidth_le
#print axioms EffectiveEncoding.binaryWidth_le
#check EffectiveEncoding.providerHeightBudget_polynomial
#print axioms EffectiveEncoding.providerHeightBudget_polynomial
#check EffectiveEncoding.extractionCode_provider_precision
#print axioms EffectiveEncoding.extractionCode_provider_precision
#check EffectiveEncoding.extractionCode_provider_integerHeight
#print axioms EffectiveEncoding.extractionCode_provider_integerHeight
#check EffectiveEncoding.extractionCode_targetCache_operations
#print axioms EffectiveEncoding.extractionCode_targetCache_operations
#check EffectiveEncoding.extractionCode_targetCache_precision
#print axioms EffectiveEncoding.extractionCode_targetCache_precision
#check EffectiveEncoding.extractionCode_targetCache_height
#print axioms EffectiveEncoding.extractionCode_targetCache_height
#check EffectiveEncoding.extractionTargetCacheOperations_bound
#print axioms EffectiveEncoding.extractionTargetCacheOperations_bound
#check EffectiveEncoding.scalarIntermediateHeights_of_budget
#print axioms EffectiveEncoding.scalarIntermediateHeights_of_budget
#check EffectiveEncoding.packetIntermediateHeights_of_budget
#print axioms EffectiveEncoding.packetIntermediateHeights_of_budget
#check EffectiveEncoding.SingleCode.packetExpression_intermediateHeights
#print axioms EffectiveEncoding.SingleCode.packetExpression_intermediateHeights
#check EffectiveEncoding.extractionCode_provider_intermediateHeights
#print axioms EffectiveEncoding.extractionCode_provider_intermediateHeights
#check EffectiveEncoding.extractionCode_targetCache_intermediateHeights
#print axioms EffectiveEncoding.extractionCode_targetCache_intermediateHeights
#check EffectiveEncoding.integerRoot_work_operand_bound
#print axioms EffectiveEncoding.integerRoot_work_operand_bound
#check EffectiveEncoding.integerTargetCache_values
#print axioms EffectiveEncoding.integerTargetCache_values
#check EffectiveEncoding.integerDescriptorSynthesis_eq
#print axioms EffectiveEncoding.integerDescriptorSynthesis_eq
#check EffectiveEncoding.integerNumericalExtractionCode_eq
#print axioms EffectiveEncoding.integerNumericalExtractionCode_eq
#check EffectiveEncoding.integerNumericalExtractionCode_error
#print axioms EffectiveEncoding.integerNumericalExtractionCode_error
#check EffectiveEncoding.integerNumericalExtractionCode_fidelity
#print axioms EffectiveEncoding.integerNumericalExtractionCode_fidelity
#check EffectiveEncoding.integerPacketBits_bound
#print axioms EffectiveEncoding.integerPacketBits_bound
#check EffectiveEncoding.extractionCode_integerTargetCacheBits
#print axioms EffectiveEncoding.extractionCode_integerTargetCacheBits
#check EffectiveEncoding.extractionWithTargetOperations_bound
#print axioms EffectiveEncoding.extractionWithTargetOperations_bound
#check EffectiveEncoding.extractionCode_provider_BitEnvelope
#print axioms EffectiveEncoding.extractionCode_provider_BitEnvelope
#check EffectiveEncoding.packetLiteral_budget_of_height
#print axioms EffectiveEncoding.packetLiteral_budget_of_height
#check EffectiveEncoding.extractionCode_cachedTarget_BitEnvelope
#print axioms EffectiveEncoding.extractionCode_cachedTarget_BitEnvelope
#check EffectiveEncoding.extractionCode_actualCachedTarget_BitEnvelope
#print axioms EffectiveEncoding.extractionCode_actualCachedTarget_BitEnvelope
#check EffectiveEncoding.constantExpression
#print axioms EffectiveEncoding.constantExpression
#check EffectiveEncoding.meanPlusExpression
#print axioms EffectiveEncoding.meanPlusExpression
#check EffectiveEncoding.halfCosExpression
#print axioms EffectiveEncoding.halfCosExpression
#check EffectiveEncoding.halfSinExpression
#print axioms EffectiveEncoding.halfSinExpression
#check EffectiveEncoding.AngleAtom.cosExpression
#print axioms EffectiveEncoding.AngleAtom.cosExpression
#check EffectiveEncoding.AngleAtom.sinExpression
#print axioms EffectiveEncoding.AngleAtom.sinExpression
#check EffectiveEncoding.AngleCode.cosExpression
#print axioms EffectiveEncoding.AngleCode.cosExpression
#check EffectiveEncoding.AngleCode.sinExpression
#print axioms EffectiveEncoding.AngleCode.sinExpression
#check EffectiveEncoding.phaseCosExpression
#print axioms EffectiveEncoding.phaseCosExpression
#check EffectiveEncoding.phaseSinExpression
#print axioms EffectiveEncoding.phaseSinExpression
#check EffectiveEncoding.SingleCode.packetExpression
#print axioms EffectiveEncoding.SingleCode.packetExpression
#check EffectiveEncoding.SingleCode.integerPacket
#print axioms EffectiveEncoding.SingleCode.integerPacket
#check EffectiveEncoding.halfExpressionBudget
#print axioms EffectiveEncoding.halfExpressionBudget
#check EffectiveEncoding.providerHeightBudget
#print axioms EffectiveEncoding.providerHeightBudget
#check EffectiveEncoding.fourMax
#print axioms EffectiveEncoding.fourMax
#check EffectiveEncoding.scalarRootPrecision
#print axioms EffectiveEncoding.scalarRootPrecision
#check EffectiveEncoding.packetRootPrecision
#print axioms EffectiveEncoding.packetRootPrecision
#check EffectiveEncoding.targetCacheOperations
#print axioms EffectiveEncoding.targetCacheOperations
#check EffectiveEncoding.gateTargetCacheOperations
#print axioms EffectiveEncoding.gateTargetCacheOperations
#check EffectiveEncoding.extractionTargetCacheOperations
#print axioms EffectiveEncoding.extractionTargetCacheOperations
#check EffectiveEncoding.scalarIntermediateHeights
#print axioms EffectiveEncoding.scalarIntermediateHeights
#check EffectiveEncoding.packetIntermediateHeights
#print axioms EffectiveEncoding.packetIntermediateHeights
#check EffectiveEncoding.integerTargetCache
#print axioms EffectiveEncoding.integerTargetCache
#check EffectiveEncoding.integerDescriptorSynthesis
#print axioms EffectiveEncoding.integerDescriptorSynthesis
#check EffectiveEncoding.integerNumericalExtractionCode
#print axioms EffectiveEncoding.integerNumericalExtractionCode
#check EffectiveEncoding.integerPacketBits
#print axioms EffectiveEncoding.integerPacketBits
#check EffectiveEncoding.integerTargetCacheBits
#print axioms EffectiveEncoding.integerTargetCacheBits
#check EffectiveEncoding.extractionWithTargetOperations
#print axioms EffectiveEncoding.extractionWithTargetOperations
