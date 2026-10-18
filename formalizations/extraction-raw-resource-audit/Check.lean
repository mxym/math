import RawResourceAudit
import RawResourceVerification.ReplaySupport

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true

run_cmd (RawResourceVerification.checkKinds [
  ``EffectiveEncoding.costedRawCachedRun_operations,
  ``EffectiveEncoding.costedRawDescriptorRun_rootCharge_polynomial,
  ``EffectiveEncoding.costedRawDescriptorRun_rootCharge_logarithmic,
  ``EffectiveEncoding.extractionRawRootCharge_bound,
  ``EffectiveEncoding.extractionRawRootCharge_polynomial,
  ``EffectiveEncoding.rawTargetProgramCache_values,
  ``EffectiveEncoding.targetProgramDescriptorRun_result,
  ``EffectiveEncoding.targetProgramDescriptorRun_rootCharge,
  ``EffectiveEncoding.targetProgramDescriptorRun_rootCharge_bound,
  ``EffectiveEncoding.chargedProviderExtractionCode_eq,
  ``EffectiveEncoding.chargedProviderExtractionCode_fidelity,
  ``EffectiveEncoding.extractionProviderProgramRootCharge_bound,
  ``EffectiveEncoding.costedRawCachedRun_result,
  ``EffectiveEncoding.costedRawCachedRun_rootCharge,
  ``EffectiveEncoding.costedRawDescriptorRun_result,
  ``EffectiveEncoding.costedRawExtractionCode_eq,
  ``EffectiveEncoding.costedRawExtractionCode_fidelity,
  ``EffectiveEncoding.costedRawDescriptorRun_integerBitBudget,
  ``EffectiveEncoding.costedRawDescriptorRun_binaryProgramOperandTrace_height,
  ``EffectiveEncoding.countedAngleFields_erase,
  ``EffectiveEncoding.countedSingleFields_erase,
  ``EffectiveEncoding.countedGateFields_erase,
  ``EffectiveEncoding.countedWordFields_erase,
  ``EffectiveEncoding.countedProgramFields_erase,
  ``EffectiveEncoding.countedAngleFields_steps,
  ``EffectiveEncoding.countedSingleFields_steps,
  ``EffectiveEncoding.countedGateFields_steps,
  ``EffectiveEncoding.countedWordFields_steps,
  ``EffectiveEncoding.extractionCode_countedFields_roundtrip,
  ``EffectiveEncoding.extractionCode_countedFields_steps,
  ``EffectiveEncoding.extractionCode_countedFields_steps_polynomial,
  ``EffectiveEncoding.AngleCode.fields_roundtrip,
  ``EffectiveEncoding.SingleCode.fields_roundtrip,
  ``EffectiveEncoding.GateCode.fields_roundtrip,
  ``EffectiveEncoding.wordFields_roundtrip,
  ``EffectiveEncoding.extractionCode_fields_roundtrip,
  ``EffectiveEncoding.AngleCode.fields_length,
  ``EffectiveEncoding.SingleCode.fields_length,
  ``EffectiveEncoding.GateCode.fields_length,
  ``EffectiveEncoding.wordFields_length,
  ``EffectiveEncoding.extractionCode_fields_length,
  ``EffectiveEncoding.actualGatePolynomial_power_bound,
  ``EffectiveEncoding.extractionCode_length_power_bound,
  ``EffectiveEncoding.extractionPrecision_logarithmic,
  ``EffectiveEncoding.rawExtraction_integerBitBudget_logarithmic,
  ``EffectiveEncoding.rawTargetCache_height_logarithmic,
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
  ``EffectiveEncoding.scalarIntermediateHeights_of_budget,
  ``EffectiveEncoding.packetIntermediateHeights_of_budget,
  ``EffectiveEncoding.SingleCode.packetExpression_intermediateHeights,
  ``EffectiveEncoding.extractionCode_provider_intermediateHeights,
  ``EffectiveEncoding.extractionCode_targetCache_intermediateHeights,
  ``EffectiveEncoding.integerRoot_work_operand_bound,
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
  ``EffectiveEncoding.extractionCode_actualCachedTarget_BitEnvelope,
  ``EffectiveEncoding.extraction_trace_subtree_polynomial,
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
  ``EffectiveEncoding.rawPacketCache_height,
  ``EffectiveEncoding.rawCachedIntegerRun_integerBitBudget,
  ``EffectiveEncoding.rawBudget_double,
  ``EffectiveEncoding.rawDescriptorRun_integerBitBudget,
  ``EffectiveEncoding.rawDescriptorRun_polynomial,
  ``EffectiveEncoding.rawExtraction_expression_budget,
  ``EffectiveEncoding.rawExtraction_expression_subtreeBound,
  ``EffectiveEncoding.rawExtraction_integerProgramRun_height,
  ``EffectiveEncoding.rawPacketCache_value,
  ``EffectiveEncoding.rawPacketCache_expression_value,
  ``EffectiveEncoding.rawCachedIntegerRun_word,
  ``EffectiveEncoding.rawDescriptorRun_word,
  ``EffectiveEncoding.rawExtractionCode_eq,
  ``EffectiveEncoding.rawExtractionCode_uses,
  ``EffectiveEncoding.rawExtractionCode_length,
  ``EffectiveEncoding.rawExtractionCode_error,
  ``EffectiveEncoding.rawExtractionCode_fidelity,
  ``EffectiveEncoding.integerScalar_ext_value,
  ``EffectiveEncoding.integerLiteral_zero,
  ``EffectiveEncoding.integerLiteral_one,
  ``EffectiveEncoding.integerLiteral_half,
  ``EffectiveEncoding.integerLiteral_halfInv,
  ``EffectiveEncoding.integerRoot_congr_value,
  ``EffectiveEncoding.rawAtomCos_eq,
  ``EffectiveEncoding.rawAtomSin_eq,
  ``EffectiveEncoding.rawHalfCos_eq,
  ``EffectiveEncoding.rawHalfSin_eq,
  ``EffectiveEncoding.AngleCode.rawCos_eq,
  ``EffectiveEncoding.AngleCode.rawSin_eq,
  ``EffectiveEncoding.rawPhaseCos_eq,
  ``EffectiveEncoding.rawPhaseSin_eq,
  ``EffectiveEncoding.SingleCode.rawPacket_eq,
  ``EffectiveEncoding.SingleCode.rawPacket_value,
  ``EffectiveEncoding.extractionCode_rawPacket_height,
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
  ``EffectiveEncoding.AngleAtom.rawCosExpression_run,
  ``EffectiveEncoding.AngleAtom.rawSinExpression_run,
  ``EffectiveEncoding.AngleCode.rawCosExpression_run,
  ``EffectiveEncoding.AngleCode.rawSinExpression_run,
  ``EffectiveEncoding.rawPhaseCosExpression_run,
  ``EffectiveEncoding.rawPhaseSinExpression_run,
  ``EffectiveEncoding.SingleCode.rawPacketExpression_run,
  ``EffectiveEncoding.SingleCode.rawPacketProgram_value,
  ``EffectiveEncoding.sharedRawCachedRun_eq,
  ``EffectiveEncoding.sharedRawDescriptorRun_eq,
  ``EffectiveEncoding.sharedRawExtractionCode_eq,
  ``EffectiveEncoding.sharedRawExtractionCode_length,
  ``EffectiveEncoding.sharedRawExtractionCode_error,
  ``EffectiveEncoding.sharedRawExtractionCode_fidelity,
  ``EffectiveEncoding.sharedRawDescriptorRun_rootCharge,
  ``EffectiveEncoding.sharedRawDescriptorRun_integerBitBudget,
  ``EffectiveEncoding.extractionSharedRawRootCharge_eq,
  ``EffectiveEncoding.extractionSharedRawRootCharge_bound,
  ``EffectiveEncoding.applyStoredSwaps_value,
  ``EffectiveEncoding.applyStoredSwaps_count,
  ``EffectiveEncoding.storedAlignmentRun_word,
  ``EffectiveEncoding.storedAlignmentRun_count,
  ``EffectiveEncoding.storedAlignmentRun_empty_word,
  ``EffectiveEncoding.storedAlignmentRun_empty_count_bound,
  ``EffectiveEncoding.storedOccupationStepCode_eq,
  ``EffectiveEncoding.storedStageCode_eq,
  ``EffectiveEncoding.storedCompressionCode_eq,
  ``EffectiveEncoding.storedExtractionCode_eq,
  ``EffectiveEncoding.storedSharedRawExtractionCode_eq,
  ``EffectiveEncoding.storedSharedRawExtractionCode_fidelity,
  ``EffectiveEncoding.stageStoredSwapApplications_exact,
  ``EffectiveEncoding.stageStoredSwapApplications_bound,
  ``EffectiveEncoding.extractionStoredSwapApplications_bound,
  ``CircuitRecursion.binaryDivDigits_invariant,
  ``CircuitRecursion.binaryDivDigits_correct,
  ``CircuitRecursion.binaryIntegerDiv_input_fuel,
  ``CircuitRecursion.binaryIntegerDivMod_eq,
  ``CircuitRecursion.binaryIntegerDiv_eq,
  ``CircuitRecursion.binaryIntegerMod_eq,
  ``CircuitRecursion.binaryIntegerDiv_operations,
  ``CircuitRecursion.binaryDivOperandTrace_height,
  ``CircuitRecursion.binarySqrtDigits_correct,
  ``CircuitRecursion.binarySqrtDigits_le_input,
  ``CircuitRecursion.binaryIntegerSqrt_eq,
  ``CircuitRecursion.binaryIntegerSqrtFuel_bound,
  ``CircuitRecursion.binarySqrtDigitOperations_eq,
  ``CircuitRecursion.binaryIntegerSqrt_operations,
  ``CircuitRecursion.binarySqrtOperandTrace_height,
  ``CircuitRecursion.binaryIntegerSqrt_operandTrace_height,
  ``CircuitRecursion.ScalarExpression.binaryProgramOperandTrace_height,
  ``CircuitRecursion.PacketExpression.binaryProgramOperandTrace_height,
  ``CircuitRecursion.ArithmeticWordResult.binaryProgramOperandTrace_height,
  ``CircuitRecursion.cachedArithmeticRun_binaryProgramOperandTrace_height,
  ``CircuitRecursion.cachedArithmeticRun_rational_binaryProgramOperandTrace_height,
  ``CircuitRecursion.IntegerScalar.binaryRoot_eq,
  ``CircuitRecursion.IntegerScalar.binaryRoot_operations,
  ``CircuitRecursion.IntegerScalar.binaryRoot_operandTrace_height,
  ``CircuitRecursion.ScalarExpression.binaryRootRun_eq,
  ``CircuitRecursion.PacketExpression.binaryRootRun_eq,
  ``CircuitRecursion.ScalarExpression.binaryRootRun_correct,
  ``CircuitRecursion.PacketExpression.binaryRootRun_correct,
  ``CircuitRecursion.IntegerScalar.binaryRootPrimitiveOperations_bound,
  ``CircuitRecursion.IntegerScalar.binaryRootOperandTrace_bound,
  ``CircuitRecursion.IntegerScalar.binaryRootOperandTrace_binaryLength,
  ``CircuitRecursion.ScalarExpression.binaryRootRun_height,
  ``CircuitRecursion.PacketExpression.binaryRootRun_height,
  ``CircuitRecursion.pairTraceT_pos,
  ``CircuitRecursion.pairTraceT_bound,
  ``CircuitRecursion.numericalThreshold_pow_bound,
  ``CircuitRecursion.traceT_threshold_bound,
  ``CircuitRecursion.pairedTraceS_step,
  ``CircuitRecursion.pairTraceS_bound,
  ``CircuitRecursion.pairedTraceR_step,
  ``CircuitRecursion.mul_extra_scale,
  ``CircuitRecursion.pairTraceR_bound,
  ``CircuitRecursion.traceRGrowth_precision_bound,
  ``CircuitRecursion.tracedPairWord_flat_integerBitBudget,
  ``CircuitRecursion.cachedIntegerBudget_algebra,
  ``CircuitRecursion.cachedArithmeticRun_eq_packetExpression,
  ``CircuitRecursion.cachedArithmeticRun_integerBitBudget,
  ``CircuitRecursion.ArithmeticWordResult.expression_integerHeight,
  ``CircuitRecursion.cachedArithmeticRun_expression_integerHeight,
  ``CircuitRecursion.ScalarExpression.costedIntegerRun_value,
  ``CircuitRecursion.PacketExpression.costedIntegerRun_value,
  ``CircuitRecursion.ScalarExpression.costedIntegerRun_rootCharge,
  ``CircuitRecursion.PacketExpression.costedIntegerRun_rootCharge,
  ``CircuitRecursion.ScalarExpression.costedIntegerRun_correct,
  ``CircuitRecursion.PacketExpression.costedIntegerRun_correct,
  ``CircuitRecursion.costedTracedBase_result,
  ``CircuitRecursion.costedTracedBase_rootCharge,
  ``CircuitRecursion.costedTracedCorrection_result,
  ``CircuitRecursion.costedTracedCorrection_rootCharge,
  ``CircuitRecursion.costedTracedPairWord_result,
  ``CircuitRecursion.costedTracedPairWord_rootCharge,
  ``CircuitRecursion.costedCachedArithmeticRun_result,
  ``CircuitRecursion.costedCachedArithmeticRun_rootCharge,
  ``CircuitRecursion.ScalarExpression.integerProgramRun_eq,
  ``CircuitRecursion.PacketExpression.integerProgramRun_eq,
  ``CircuitRecursion.ScalarExpression.integerProgramRun_correct,
  ``CircuitRecursion.PacketExpression.integerProgramRun_correct,
  ``CircuitRecursion.integerTracedBase_eq,
  ``CircuitRecursion.integerTracedCorrection_eq,
  ``CircuitRecursion.integerTracedCorrection_function,
  ``CircuitRecursion.integerTracedPairWord_eq,
  ``CircuitRecursion.integerCachedArithmeticRun_eq,
  ``CircuitRecursion.integerCachedArithmeticRun_rational_integerBitBudget,
  ``CircuitRecursion.integerCachedArithmeticSU2Synthesis,
  ``CircuitRecursion.IntegerScalar.crossLE_value,
  ``CircuitRecursion.integerMinIndex_eq,
  ``CircuitRecursion.integerMaxIndex_eq,
  ``CircuitRecursion.IntegerScalar.crossLE_operands_height,
  ``CircuitRecursion.ScalarExpression.integerSubtreeBound,
  ``CircuitRecursion.PacketExpression.integerSubtreeBound,
  ``CircuitRecursion.ArithmeticWordResult.expression_integerSubtreeBound,
  ``CircuitRecursion.cachedArithmeticRun_expression_integerSubtreeBound,
  ``CircuitRecursion.bitFactorEnvelope_closed,
  ``CircuitRecursion.tracedBase_integerBitBudget,
  ``CircuitRecursion.tracedCorrection_integerBitBudget,
  ``CircuitRecursion.tracedPairWord_integerBitBudget,
  ``CircuitRecursion.cachedRationalPacketExpression_bitEnvelope,
  ``CircuitRecursion.cachedArithmeticRun_eq_rationalPacketExpression,
  ``CircuitRecursion.cachedArithmeticRun_envelope_integerBitBudget,
  ``CircuitRecursion.cachedArithmeticRun_rational_integerBitBudget,
  ``CircuitRecursion.cachedArithmeticRun_rational_expression_integerSubtreeBound,
  ``CircuitRecursion.IntegerScalar.ofRat_intCast,
  ``CircuitRecursion.IntegerScalar.ofInt_positive_inv,
  ``CircuitRecursion.rawScalarExpression_integerProgramRun,
  ``CircuitRecursion.rawPacketExpression_integerProgramRun,
  ``CircuitRecursion.rawPacketExpression_eval,
  ``CircuitRecursion.rawScalarExpression_operations,
  ``CircuitRecursion.rawPacketExpression_operations,
  ``CircuitRecursion.rationalBinaryExponent_intCast_le,
  ``CircuitRecursion.rawScalarExpression_integerBitBudget,
  ``CircuitRecursion.rawPacketExpression_integerBitBudget,
  ``CircuitRecursion.rawPacketExpression_integerProgramRun_height,
  ``CircuitRecursion.rawPacketExpressionOracle_eval,
  ``CircuitRecursion.rawPacketExpressionOracle_bitEnvelope,
  ``CircuitRecursion.rawCorrectionOperationOffset_le,
  ``CircuitRecursion.rawPairOperationOffset_le,
  ``CircuitRecursion.tracedPairWord_twenty_operations,
  ``CircuitRecursion.tracedPairWord_twenty_precision_operations,
  ``CircuitRecursion.rawPacketExpressionOracle_operationBound,
  ``CircuitRecursion.costedRawPacketPairWord_operations,
  ``CircuitRecursion.costedTracedPairWord_twenty_rootCharge,
  ``CircuitRecursion.rawExpressionWord_bound,
  ``CircuitRecursion.rawTracedBase_operations,
  ``CircuitRecursion.rawTracedCorrection_operations,
  ``CircuitRecursion.rawTracedPairWord_operations,
  ``CircuitRecursion.natural_le_power_two,
  ``CircuitRecursion.IntegerScalar.rootOperandTrace_height,
  ``CircuitRecursion.integerStoppingThresholdOperandTrace_height,
  ``CircuitRecursion.IntegerScalar.rootOperandTrace_binaryLength,
  ``CircuitRecursion.IntegerScalar.root_numerator_in_operandTrace,
  ``CircuitRecursion.IntegerScalar.root_denominator_in_operandTrace,
  ``CircuitRecursion.ScalarExpression.binaryRootPrimitiveOperations_bound,
  ``CircuitRecursion.PacketExpression.binaryRootPrimitiveOperations_bound,
  ``CircuitRecursion.ArithmeticWordResult.binaryRootPrimitiveOperations_bound,
  ``CircuitRecursion.cachedArithmeticRun_binaryRootPrimitiveOperations,
  ``CircuitRecursion.cachedArithmeticRun_envelope_binaryRootPrimitiveOperations,
  ``CircuitRecursion.cachedRootCost_algebra,
  ``CircuitRecursion.cachedArithmeticRun_binaryRootPrimitiveOperations_polynomial,
  ``CircuitRecursion.ScalarExpression.rootOperandTrace_height,
  ``CircuitRecursion.PacketExpression.rootOperandTrace_height,
  ``CircuitRecursion.ArithmeticWordResult.rootOperandTrace_height,
  ``CircuitRecursion.cachedArithmeticRun_rootOperandTrace_height,
  ``CircuitRecursion.cachedArithmeticRun_rational_rootOperandTrace_height,
  ``CircuitRecursion.IntegerScalar.sharedBinaryRoot_quotient,
  ``CircuitRecursion.IntegerScalar.sharedBinaryRoot_value,
  ``CircuitRecursion.IntegerScalar.sharedBinaryRoot_charge,
  ``CircuitRecursion.IntegerScalar.sharedBinaryRoot_eq,
  ``CircuitRecursion.IntegerScalar.sharedBinaryRoot_correct,
  ``CircuitRecursion.IntegerScalar.sharedBinaryRoot_height,
  ``CircuitRecursion.IntegerScalar.sharedBinaryRoot_charge_bound,
  ``CircuitRecursion.ScalarExpression.sharedCostedIntegerRun_eq,
  ``CircuitRecursion.PacketExpression.sharedCostedIntegerRun_eq,
  ``CircuitRecursion.sharedCostedTracedBase_eq,
  ``CircuitRecursion.sharedCostedTracedCorrection_eq,
  ``CircuitRecursion.sharedCostedTracedPairWord_eq,
  ``CircuitRecursion.sharedCostedCachedArithmeticRun_eq,
  ``CircuitRecursion.ScalarExpression.sharedCostedIntegerRun_value,
  ``CircuitRecursion.PacketExpression.sharedCostedIntegerRun_value,
  ``CircuitRecursion.ScalarExpression.sharedCostedIntegerRun_rootCharge,
  ``CircuitRecursion.PacketExpression.sharedCostedIntegerRun_rootCharge,
  ``CircuitRecursion.ScalarExpression.sharedCostedIntegerRun_correct,
  ``CircuitRecursion.PacketExpression.sharedCostedIntegerRun_correct,
  ``CircuitRecursion.sharedCostedTracedBase_result,
  ``CircuitRecursion.sharedCostedTracedBase_rootCharge,
  ``CircuitRecursion.sharedCostedTracedCorrection_result,
  ``CircuitRecursion.sharedCostedTracedCorrection_rootCharge,
  ``CircuitRecursion.sharedCostedTracedPairWord_result,
  ``CircuitRecursion.sharedCostedTracedPairWord_rootCharge,
  ``CircuitRecursion.sharedCostedCachedArithmeticRun_result,
  ``CircuitRecursion.sharedCostedCachedArithmeticRun_rootCharge
] [
  ``EffectiveEncoding.actualRawRootCoefficient,
  ``EffectiveEncoding.gateRawRootCharge,
  ``EffectiveEncoding.extractionRawRootCharge,
  ``EffectiveEncoding.rawTargetProgramCache,
  ``EffectiveEncoding.targetProgramDescriptorRun,
  ``EffectiveEncoding.chargedProviderExtractionCode,
  ``EffectiveEncoding.gateProviderProgramRootCharge,
  ``EffectiveEncoding.extractionProviderProgramRootCharge,
  ``EffectiveEncoding.costedRawCachedRun,
  ``EffectiveEncoding.costedRawDescriptorRun,
  ``EffectiveEncoding.costedRawExtractionCode,
  ``EffectiveEncoding.FieldRun,
  ``EffectiveEncoding.FieldRun.empty,
  ``EffectiveEncoding.FieldRun.emit,
  ``EffectiveEncoding.FieldRun.append,
  ``EffectiveEncoding.countedAngleFields,
  ``EffectiveEncoding.countedSingleFields,
  ``EffectiveEncoding.countedGateFields,
  ``EffectiveEncoding.countedWordFields,
  ``EffectiveEncoding.countedProgramFields,
  ``EffectiveEncoding.AngleCode.fields,
  ``EffectiveEncoding.parseAngleFields,
  ``EffectiveEncoding.SingleCode.fields,
  ``EffectiveEncoding.parseSingleFields,
  ``EffectiveEncoding.GateCode.fields,
  ``EffectiveEncoding.parseGateFields,
  ``EffectiveEncoding.wordFields,
  ``EffectiveEncoding.parseWordFields,
  ``EffectiveEncoding.programFields,
  ``EffectiveEncoding.parseProgramFields,
  ``EffectiveEncoding.logarithmicPrecision,
  ``EffectiveEncoding.rawLogarithmicOperandBudget,
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
  ``EffectiveEncoding.scalarIntermediateHeights,
  ``EffectiveEncoding.packetIntermediateHeights,
  ``EffectiveEncoding.fourMax,
  ``EffectiveEncoding.scalarRootPrecision,
  ``EffectiveEncoding.packetRootPrecision,
  ``EffectiveEncoding.targetCacheOperations,
  ``EffectiveEncoding.gateTargetCacheOperations,
  ``EffectiveEncoding.extractionTargetCacheOperations,
  ``EffectiveEncoding.integerTargetCache,
  ``EffectiveEncoding.integerDescriptorSynthesis,
  ``EffectiveEncoding.integerNumericalExtractionCode,
  ``EffectiveEncoding.integerPacketBits,
  ``EffectiveEncoding.integerTargetCacheBits,
  ``EffectiveEncoding.extractionWithTargetOperations,
  ``EffectiveEncoding.actualTargetCacheHeight,
  ``EffectiveEncoding.actualDescriptorTraceBudget,
  ``EffectiveEncoding.actualTraceConstant,
  ``EffectiveEncoding.actualGatePolynomial,
  ``EffectiveEncoding.pipelinePrecisionPolynomial,
  ``EffectiveEncoding.extractionOperandPolynomial,
  ``EffectiveEncoding.buildRawPacketCache,
  ``EffectiveEncoding.readRawPacketCache,
  ``EffectiveEncoding.rawCachedIntegerRun,
  ``EffectiveEncoding.rawDescriptorRun,
  ``EffectiveEncoding.rawExtractionCode,
  ``EffectiveEncoding.integerFraction,
  ``EffectiveEncoding.integerHalf,
  ``EffectiveEncoding.rawAtomCos,
  ``EffectiveEncoding.rawAtomSin,
  ``EffectiveEncoding.RawScalarOracle,
  ``EffectiveEncoding.rawHalfCos,
  ``EffectiveEncoding.rawHalfSin,
  ``EffectiveEncoding.AngleCode.rawCos,
  ``EffectiveEncoding.AngleCode.rawSin,
  ``EffectiveEncoding.rawPhaseCos,
  ``EffectiveEncoding.rawPhaseSin,
  ``EffectiveEncoding.SingleCode.rawPacket,
  ``EffectiveEncoding.rawProviderHeightBudget,
  ``EffectiveEncoding.rawTargetProgramCacheCharge,
  ``EffectiveEncoding.rawProviderRootBudget,
  ``EffectiveEncoding.rawProviderCacheRootCoefficient,
  ``EffectiveEncoding.rawProviderCachePolynomialConstant,
  ``EffectiveEncoding.AngleAtom.rawCosExpression,
  ``EffectiveEncoding.AngleAtom.rawSinExpression,
  ``EffectiveEncoding.AngleCode.rawCosExpression,
  ``EffectiveEncoding.AngleCode.rawSinExpression,
  ``EffectiveEncoding.rawPhaseCosExpression,
  ``EffectiveEncoding.rawPhaseSinExpression,
  ``EffectiveEncoding.SingleCode.rawPacketExpression,
  ``EffectiveEncoding.SingleCode.rawPacketProgram,
  ``EffectiveEncoding.sharedRawCachedRun,
  ``EffectiveEncoding.sharedRawDescriptorRun,
  ``EffectiveEncoding.sharedRawExtractionCode,
  ``EffectiveEncoding.gateSharedRawRootCharge,
  ``EffectiveEncoding.extractionSharedRawRootCharge,
  ``EffectiveEncoding.StoredSwaps,
  ``EffectiveEncoding.applyStoredSwaps,
  ``EffectiveEncoding.storedSwapPermutation,
  ``EffectiveEncoding.StoredAlignmentRun,
  ``EffectiveEncoding.storedAlignmentRun,
  ``EffectiveEncoding.storedOccupationStepCode,
  ``EffectiveEncoding.storedStageCode,
  ``EffectiveEncoding.storedCompressionCode,
  ``EffectiveEncoding.storedExtractionCode,
  ``EffectiveEncoding.storedSharedRawExtractionCode,
  ``EffectiveEncoding.stageStoredSwapApplications,
  ``EffectiveEncoding.extractionStoredSwapApplications,
  ``CircuitRecursion.binaryDivDigits,
  ``CircuitRecursion.binaryIntegerDivMod,
  ``CircuitRecursion.binaryIntegerDiv,
  ``CircuitRecursion.binaryIntegerMod,
  ``CircuitRecursion.binaryDivDigitOperations,
  ``CircuitRecursion.binaryDivOperandTrace,
  ``CircuitRecursion.binarySqrtDigits,
  ``CircuitRecursion.binaryIntegerSqrtFuel,
  ``CircuitRecursion.binaryIntegerSqrt,
  ``CircuitRecursion.binarySqrtDigitOperations,
  ``CircuitRecursion.binarySqrtOperandTrace,
  ``CircuitRecursion.ScalarExpression.binaryProgramOperandTrace,
  ``CircuitRecursion.PacketExpression.binaryProgramOperandTrace,
  ``CircuitRecursion.ArithmeticWordResult.binaryProgramOperandTrace,
  ``CircuitRecursion.IntegerScalar.binaryRoot,
  ``CircuitRecursion.ScalarExpression.binaryRootRun,
  ``CircuitRecursion.PacketExpression.binaryRootRun,
  ``CircuitRecursion.IntegerScalar.binaryRootPrimitiveOperations,
  ``CircuitRecursion.IntegerScalar.binaryRootOperandTrace,
  ``CircuitRecursion.traceTGrowth,
  ``CircuitRecursion.traceSGrowth,
  ``CircuitRecursion.traceRGrowth,
  ``CircuitRecursion.cachedIntegerBudgetConstant,
  ``CircuitRecursion.ScalarIntegerEvaluation,
  ``CircuitRecursion.PacketIntegerEvaluation,
  ``CircuitRecursion.ScalarExpression.costedIntegerRun,
  ``CircuitRecursion.PacketExpression.costedIntegerRun,
  ``CircuitRecursion.CostedArithmeticWordResult,
  ``CircuitRecursion.costedTracedBase,
  ``CircuitRecursion.costedTracedCorrection,
  ``CircuitRecursion.costedTracedPairWord,
  ``CircuitRecursion.costedCachedArithmeticRun,
  ``CircuitRecursion.ScalarExpression.integerProgramRun,
  ``CircuitRecursion.PacketExpression.integerProgramRun,
  ``CircuitRecursion.integerTracedBase,
  ``CircuitRecursion.integerTracedCorrection,
  ``CircuitRecursion.integerTracedPairWord,
  ``CircuitRecursion.integerCachedArithmeticRun,
  ``CircuitRecursion.IntegerScalar.crossLE,
  ``CircuitRecursion.integerMinIndex,
  ``CircuitRecursion.integerMaxIndex,
  ``CircuitRecursion.ScalarExpression.IntegerSubtreeBound,
  ``CircuitRecursion.PacketExpression.IntegerSubtreeBound,
  ``CircuitRecursion.ArithmeticWordResult.integerBitBudget,
  ``CircuitRecursion.TraceBitBound,
  ``CircuitRecursion.correctionTraceS,
  ``CircuitRecursion.correctionTraceT,
  ``CircuitRecursion.correctionTraceR,
  ``CircuitRecursion.pairTraceT,
  ``CircuitRecursion.pairTraceS,
  ``CircuitRecursion.pairTraceR,
  ``CircuitRecursion.PacketOracleHeight,
  ``CircuitRecursion.cachedRationalPacketExpression,
  ``CircuitRecursion.rawScalarExpression,
  ``CircuitRecursion.rawPacketExpression,
  ``CircuitRecursion.rawPacketExpressionOracle,
  ``CircuitRecursion.rawCorrectionOperationOffset,
  ``CircuitRecursion.rawPairOperationOffset,
  ``CircuitRecursion.IntegerScalar.rootOperandTrace,
  ``CircuitRecursion.integerStoppingThresholdOperandTrace,
  ``CircuitRecursion.ScalarExpression.binaryRootPrimitiveOperations,
  ``CircuitRecursion.PacketExpression.binaryRootPrimitiveOperations,
  ``CircuitRecursion.ArithmeticWordResult.binaryRootPrimitiveOperations,
  ``CircuitRecursion.ScalarExpression.rootOperandTrace,
  ``CircuitRecursion.PacketExpression.rootOperandTrace,
  ``CircuitRecursion.ArithmeticWordResult.rootOperandTrace,
  ``CircuitRecursion.IntegerScalar.sharedBinaryRoot,
  ``CircuitRecursion.ScalarExpression.sharedCostedIntegerRun,
  ``CircuitRecursion.PacketExpression.sharedCostedIntegerRun,
  ``CircuitRecursion.sharedCostedTracedBase,
  ``CircuitRecursion.sharedCostedTracedCorrection,
  ``CircuitRecursion.sharedCostedTracedPairWord,
  ``CircuitRecursion.sharedCostedCachedArithmeticRun
])

#check EffectiveEncoding.costedRawCachedRun_operations
set_option pp.universes false in #print axioms EffectiveEncoding.costedRawCachedRun_operations
#check EffectiveEncoding.costedRawDescriptorRun_rootCharge_polynomial
set_option pp.universes false in #print axioms EffectiveEncoding.costedRawDescriptorRun_rootCharge_polynomial
#check EffectiveEncoding.costedRawDescriptorRun_rootCharge_logarithmic
set_option pp.universes false in #print axioms EffectiveEncoding.costedRawDescriptorRun_rootCharge_logarithmic
#check EffectiveEncoding.extractionRawRootCharge_bound
set_option pp.universes false in #print axioms EffectiveEncoding.extractionRawRootCharge_bound
#check EffectiveEncoding.extractionRawRootCharge_polynomial
set_option pp.universes false in #print axioms EffectiveEncoding.extractionRawRootCharge_polynomial
#check EffectiveEncoding.rawTargetProgramCache_values
set_option pp.universes false in #print axioms EffectiveEncoding.rawTargetProgramCache_values
#check EffectiveEncoding.targetProgramDescriptorRun_result
set_option pp.universes false in #print axioms EffectiveEncoding.targetProgramDescriptorRun_result
#check EffectiveEncoding.targetProgramDescriptorRun_rootCharge
set_option pp.universes false in #print axioms EffectiveEncoding.targetProgramDescriptorRun_rootCharge
#check EffectiveEncoding.targetProgramDescriptorRun_rootCharge_bound
set_option pp.universes false in #print axioms EffectiveEncoding.targetProgramDescriptorRun_rootCharge_bound
#check EffectiveEncoding.chargedProviderExtractionCode_eq
set_option pp.universes false in #print axioms EffectiveEncoding.chargedProviderExtractionCode_eq
#check EffectiveEncoding.chargedProviderExtractionCode_fidelity
set_option pp.universes false in #print axioms EffectiveEncoding.chargedProviderExtractionCode_fidelity
#check EffectiveEncoding.extractionProviderProgramRootCharge_bound
set_option pp.universes false in #print axioms EffectiveEncoding.extractionProviderProgramRootCharge_bound
#check EffectiveEncoding.costedRawCachedRun_result
set_option pp.universes false in #print axioms EffectiveEncoding.costedRawCachedRun_result
#check EffectiveEncoding.costedRawCachedRun_rootCharge
set_option pp.universes false in #print axioms EffectiveEncoding.costedRawCachedRun_rootCharge
#check EffectiveEncoding.costedRawDescriptorRun_result
set_option pp.universes false in #print axioms EffectiveEncoding.costedRawDescriptorRun_result
#check EffectiveEncoding.costedRawExtractionCode_eq
set_option pp.universes false in #print axioms EffectiveEncoding.costedRawExtractionCode_eq
#check EffectiveEncoding.costedRawExtractionCode_fidelity
set_option pp.universes false in #print axioms EffectiveEncoding.costedRawExtractionCode_fidelity
#check EffectiveEncoding.costedRawDescriptorRun_integerBitBudget
set_option pp.universes false in #print axioms EffectiveEncoding.costedRawDescriptorRun_integerBitBudget
#check EffectiveEncoding.costedRawDescriptorRun_binaryProgramOperandTrace_height
set_option pp.universes false in #print axioms EffectiveEncoding.costedRawDescriptorRun_binaryProgramOperandTrace_height
#check EffectiveEncoding.countedAngleFields_erase
set_option pp.universes false in #print axioms EffectiveEncoding.countedAngleFields_erase
#check EffectiveEncoding.countedSingleFields_erase
set_option pp.universes false in #print axioms EffectiveEncoding.countedSingleFields_erase
#check EffectiveEncoding.countedGateFields_erase
set_option pp.universes false in #print axioms EffectiveEncoding.countedGateFields_erase
#check EffectiveEncoding.countedWordFields_erase
set_option pp.universes false in #print axioms EffectiveEncoding.countedWordFields_erase
#check EffectiveEncoding.countedProgramFields_erase
set_option pp.universes false in #print axioms EffectiveEncoding.countedProgramFields_erase
#check EffectiveEncoding.countedAngleFields_steps
set_option pp.universes false in #print axioms EffectiveEncoding.countedAngleFields_steps
#check EffectiveEncoding.countedSingleFields_steps
set_option pp.universes false in #print axioms EffectiveEncoding.countedSingleFields_steps
#check EffectiveEncoding.countedGateFields_steps
set_option pp.universes false in #print axioms EffectiveEncoding.countedGateFields_steps
#check EffectiveEncoding.countedWordFields_steps
set_option pp.universes false in #print axioms EffectiveEncoding.countedWordFields_steps
#check EffectiveEncoding.extractionCode_countedFields_roundtrip
set_option pp.universes false in #print axioms EffectiveEncoding.extractionCode_countedFields_roundtrip
#check EffectiveEncoding.extractionCode_countedFields_steps
set_option pp.universes false in #print axioms EffectiveEncoding.extractionCode_countedFields_steps
#check EffectiveEncoding.extractionCode_countedFields_steps_polynomial
set_option pp.universes false in #print axioms EffectiveEncoding.extractionCode_countedFields_steps_polynomial
#check EffectiveEncoding.AngleCode.fields_roundtrip
set_option pp.universes false in #print axioms EffectiveEncoding.AngleCode.fields_roundtrip
#check EffectiveEncoding.SingleCode.fields_roundtrip
set_option pp.universes false in #print axioms EffectiveEncoding.SingleCode.fields_roundtrip
#check EffectiveEncoding.GateCode.fields_roundtrip
set_option pp.universes false in #print axioms EffectiveEncoding.GateCode.fields_roundtrip
#check EffectiveEncoding.wordFields_roundtrip
set_option pp.universes false in #print axioms EffectiveEncoding.wordFields_roundtrip
#check EffectiveEncoding.extractionCode_fields_roundtrip
set_option pp.universes false in #print axioms EffectiveEncoding.extractionCode_fields_roundtrip
#check EffectiveEncoding.AngleCode.fields_length
set_option pp.universes false in #print axioms EffectiveEncoding.AngleCode.fields_length
#check EffectiveEncoding.SingleCode.fields_length
set_option pp.universes false in #print axioms EffectiveEncoding.SingleCode.fields_length
#check EffectiveEncoding.GateCode.fields_length
set_option pp.universes false in #print axioms EffectiveEncoding.GateCode.fields_length
#check EffectiveEncoding.wordFields_length
set_option pp.universes false in #print axioms EffectiveEncoding.wordFields_length
#check EffectiveEncoding.extractionCode_fields_length
set_option pp.universes false in #print axioms EffectiveEncoding.extractionCode_fields_length
#check EffectiveEncoding.actualGatePolynomial_power_bound
set_option pp.universes false in #print axioms EffectiveEncoding.actualGatePolynomial_power_bound
#check EffectiveEncoding.extractionCode_length_power_bound
set_option pp.universes false in #print axioms EffectiveEncoding.extractionCode_length_power_bound
#check EffectiveEncoding.extractionPrecision_logarithmic
set_option pp.universes false in #print axioms EffectiveEncoding.extractionPrecision_logarithmic
#check EffectiveEncoding.rawExtraction_integerBitBudget_logarithmic
set_option pp.universes false in #print axioms EffectiveEncoding.rawExtraction_integerBitBudget_logarithmic
#check EffectiveEncoding.rawTargetCache_height_logarithmic
set_option pp.universes false in #print axioms EffectiveEncoding.rawTargetCache_height_logarithmic
#check EffectiveEncoding.meanPlusExpression_eval
set_option pp.universes false in #print axioms EffectiveEncoding.meanPlusExpression_eval
#check EffectiveEncoding.halfCosExpression_eval
set_option pp.universes false in #print axioms EffectiveEncoding.halfCosExpression_eval
#check EffectiveEncoding.halfSinExpression_eval
set_option pp.universes false in #print axioms EffectiveEncoding.halfSinExpression_eval
#check EffectiveEncoding.AngleAtom.cosExpression_eval
set_option pp.universes false in #print axioms EffectiveEncoding.AngleAtom.cosExpression_eval
#check EffectiveEncoding.AngleAtom.sinExpression_eval
set_option pp.universes false in #print axioms EffectiveEncoding.AngleAtom.sinExpression_eval
#check EffectiveEncoding.AngleCode.cosExpression_eval
set_option pp.universes false in #print axioms EffectiveEncoding.AngleCode.cosExpression_eval
#check EffectiveEncoding.AngleCode.sinExpression_eval
set_option pp.universes false in #print axioms EffectiveEncoding.AngleCode.sinExpression_eval
#check EffectiveEncoding.phaseCosExpression_eval
set_option pp.universes false in #print axioms EffectiveEncoding.phaseCosExpression_eval
#check EffectiveEncoding.phaseSinExpression_eval
set_option pp.universes false in #print axioms EffectiveEncoding.phaseSinExpression_eval
#check EffectiveEncoding.SingleCode.packetExpression_eval
set_option pp.universes false in #print axioms EffectiveEncoding.SingleCode.packetExpression_eval
#check EffectiveEncoding.SingleCode.integerPacket_value
set_option pp.universes false in #print axioms EffectiveEncoding.SingleCode.integerPacket_value
#check EffectiveEncoding.halfCosExpression_operations
set_option pp.universes false in #print axioms EffectiveEncoding.halfCosExpression_operations
#check EffectiveEncoding.halfSinExpression_operations
set_option pp.universes false in #print axioms EffectiveEncoding.halfSinExpression_operations
#check EffectiveEncoding.AngleAtom.expression_operations
set_option pp.universes false in #print axioms EffectiveEncoding.AngleAtom.expression_operations
#check EffectiveEncoding.AngleCode.expression_operations
set_option pp.universes false in #print axioms EffectiveEncoding.AngleCode.expression_operations
#check EffectiveEncoding.SingleCode.packetExpression_operations
set_option pp.universes false in #print axioms EffectiveEncoding.SingleCode.packetExpression_operations
#check EffectiveEncoding.ratioLiteral_budget
set_option pp.universes false in #print axioms EffectiveEncoding.ratioLiteral_budget
#check EffectiveEncoding.AngleAtom.expression_budget
set_option pp.universes false in #print axioms EffectiveEncoding.AngleAtom.expression_budget
#check EffectiveEncoding.halfExpressionBudget_mono
set_option pp.universes false in #print axioms EffectiveEncoding.halfExpressionBudget_mono
#check EffectiveEncoding.halfExpressionBudget_ge
set_option pp.universes false in #print axioms EffectiveEncoding.halfExpressionBudget_ge
#check EffectiveEncoding.halfCosExpression_budget
set_option pp.universes false in #print axioms EffectiveEncoding.halfCosExpression_budget
#check EffectiveEncoding.halfSinExpression_budget
set_option pp.universes false in #print axioms EffectiveEncoding.halfSinExpression_budget
#check EffectiveEncoding.AngleCode.expression_budget
set_option pp.universes false in #print axioms EffectiveEncoding.AngleCode.expression_budget
#check EffectiveEncoding.SingleCode.packetExpression_budget
set_option pp.universes false in #print axioms EffectiveEncoding.SingleCode.packetExpression_budget
#check EffectiveEncoding.SingleCode.integerPacket_height
set_option pp.universes false in #print axioms EffectiveEncoding.SingleCode.integerPacket_height
#check EffectiveEncoding.extractionCode_provider_resources
set_option pp.universes false in #print axioms EffectiveEncoding.extractionCode_provider_resources
#check EffectiveEncoding.scalarIntermediateHeights_of_budget
set_option pp.universes false in #print axioms EffectiveEncoding.scalarIntermediateHeights_of_budget
#check EffectiveEncoding.packetIntermediateHeights_of_budget
set_option pp.universes false in #print axioms EffectiveEncoding.packetIntermediateHeights_of_budget
#check EffectiveEncoding.SingleCode.packetExpression_intermediateHeights
set_option pp.universes false in #print axioms EffectiveEncoding.SingleCode.packetExpression_intermediateHeights
#check EffectiveEncoding.extractionCode_provider_intermediateHeights
set_option pp.universes false in #print axioms EffectiveEncoding.extractionCode_provider_intermediateHeights
#check EffectiveEncoding.extractionCode_targetCache_intermediateHeights
set_option pp.universes false in #print axioms EffectiveEncoding.extractionCode_targetCache_intermediateHeights
#check EffectiveEncoding.integerRoot_work_operand_bound
set_option pp.universes false in #print axioms EffectiveEncoding.integerRoot_work_operand_bound
#check EffectiveEncoding.fourMax_le
set_option pp.universes false in #print axioms EffectiveEncoding.fourMax_le
#check EffectiveEncoding.halfCosExpression_precision
set_option pp.universes false in #print axioms EffectiveEncoding.halfCosExpression_precision
#check EffectiveEncoding.halfSinExpression_precision
set_option pp.universes false in #print axioms EffectiveEncoding.halfSinExpression_precision
#check EffectiveEncoding.AngleAtom.expression_precision
set_option pp.universes false in #print axioms EffectiveEncoding.AngleAtom.expression_precision
#check EffectiveEncoding.AngleCode.expression_precision
set_option pp.universes false in #print axioms EffectiveEncoding.AngleCode.expression_precision
#check EffectiveEncoding.SingleCode.packetExpression_precision
set_option pp.universes false in #print axioms EffectiveEncoding.SingleCode.packetExpression_precision
#check EffectiveEncoding.halvingBudget_power
set_option pp.universes false in #print axioms EffectiveEncoding.halvingBudget_power
#check EffectiveEncoding.binaryWidth_le
set_option pp.universes false in #print axioms EffectiveEncoding.binaryWidth_le
#check EffectiveEncoding.providerHeightBudget_polynomial
set_option pp.universes false in #print axioms EffectiveEncoding.providerHeightBudget_polynomial
#check EffectiveEncoding.extractionCode_provider_precision
set_option pp.universes false in #print axioms EffectiveEncoding.extractionCode_provider_precision
#check EffectiveEncoding.extractionCode_provider_integerHeight
set_option pp.universes false in #print axioms EffectiveEncoding.extractionCode_provider_integerHeight
#check EffectiveEncoding.extractionCode_targetCache_operations
set_option pp.universes false in #print axioms EffectiveEncoding.extractionCode_targetCache_operations
#check EffectiveEncoding.extractionCode_targetCache_precision
set_option pp.universes false in #print axioms EffectiveEncoding.extractionCode_targetCache_precision
#check EffectiveEncoding.extractionCode_targetCache_height
set_option pp.universes false in #print axioms EffectiveEncoding.extractionCode_targetCache_height
#check EffectiveEncoding.extractionTargetCacheOperations_bound
set_option pp.universes false in #print axioms EffectiveEncoding.extractionTargetCacheOperations_bound
#check EffectiveEncoding.integerTargetCache_values
set_option pp.universes false in #print axioms EffectiveEncoding.integerTargetCache_values
#check EffectiveEncoding.integerDescriptorSynthesis_eq
set_option pp.universes false in #print axioms EffectiveEncoding.integerDescriptorSynthesis_eq
#check EffectiveEncoding.integerNumericalExtractionCode_eq
set_option pp.universes false in #print axioms EffectiveEncoding.integerNumericalExtractionCode_eq
#check EffectiveEncoding.integerNumericalExtractionCode_error
set_option pp.universes false in #print axioms EffectiveEncoding.integerNumericalExtractionCode_error
#check EffectiveEncoding.integerNumericalExtractionCode_fidelity
set_option pp.universes false in #print axioms EffectiveEncoding.integerNumericalExtractionCode_fidelity
#check EffectiveEncoding.integerPacketBits_bound
set_option pp.universes false in #print axioms EffectiveEncoding.integerPacketBits_bound
#check EffectiveEncoding.extractionCode_integerTargetCacheBits
set_option pp.universes false in #print axioms EffectiveEncoding.extractionCode_integerTargetCacheBits
#check EffectiveEncoding.extractionWithTargetOperations_bound
set_option pp.universes false in #print axioms EffectiveEncoding.extractionWithTargetOperations_bound
#check EffectiveEncoding.extractionCode_provider_BitEnvelope
set_option pp.universes false in #print axioms EffectiveEncoding.extractionCode_provider_BitEnvelope
#check EffectiveEncoding.packetLiteral_budget_of_height
set_option pp.universes false in #print axioms EffectiveEncoding.packetLiteral_budget_of_height
#check EffectiveEncoding.extractionCode_cachedTarget_BitEnvelope
set_option pp.universes false in #print axioms EffectiveEncoding.extractionCode_cachedTarget_BitEnvelope
#check EffectiveEncoding.extractionCode_actualCachedTarget_BitEnvelope
set_option pp.universes false in #print axioms EffectiveEncoding.extractionCode_actualCachedTarget_BitEnvelope
#check EffectiveEncoding.extraction_trace_subtree_polynomial
set_option pp.universes false in #print axioms EffectiveEncoding.extraction_trace_subtree_polynomial
#check EffectiveEncoding.actualTargetCacheHeight_ge
set_option pp.universes false in #print axioms EffectiveEncoding.actualTargetCacheHeight_ge
#check EffectiveEncoding.actualTarget_PacketOracleHeight
set_option pp.universes false in #print axioms EffectiveEncoding.actualTarget_PacketOracleHeight
#check EffectiveEncoding.actualGate_PacketOracleHeight
set_option pp.universes false in #print axioms EffectiveEncoding.actualGate_PacketOracleHeight
#check EffectiveEncoding.actualDescriptorTrace_integerBitBudget
set_option pp.universes false in #print axioms EffectiveEncoding.actualDescriptorTrace_integerBitBudget
#check EffectiveEncoding.actualDescriptorTraceBudget_polynomial
set_option pp.universes false in #print axioms EffectiveEncoding.actualDescriptorTraceBudget_polynomial
#check EffectiveEncoding.actualDescriptorTrace_polynomial
set_option pp.universes false in #print axioms EffectiveEncoding.actualDescriptorTrace_polynomial
#check EffectiveEncoding.actualDescriptorTrace_subtreeBound
set_option pp.universes false in #print axioms EffectiveEncoding.actualDescriptorTrace_subtreeBound
#check EffectiveEncoding.extractionCode_length_polynomial
set_option pp.universes false in #print axioms EffectiveEncoding.extractionCode_length_polynomial
#check EffectiveEncoding.extractionPrecision_polynomial
set_option pp.universes false in #print axioms EffectiveEncoding.extractionPrecision_polynomial
#check EffectiveEncoding.extraction_provider_subtree_polynomial
set_option pp.universes false in #print axioms EffectiveEncoding.extraction_provider_subtree_polynomial
#check EffectiveEncoding.rawPacketCache_height
set_option pp.universes false in #print axioms EffectiveEncoding.rawPacketCache_height
#check EffectiveEncoding.rawCachedIntegerRun_integerBitBudget
set_option pp.universes false in #print axioms EffectiveEncoding.rawCachedIntegerRun_integerBitBudget
#check EffectiveEncoding.rawBudget_double
set_option pp.universes false in #print axioms EffectiveEncoding.rawBudget_double
#check EffectiveEncoding.rawDescriptorRun_integerBitBudget
set_option pp.universes false in #print axioms EffectiveEncoding.rawDescriptorRun_integerBitBudget
#check EffectiveEncoding.rawDescriptorRun_polynomial
set_option pp.universes false in #print axioms EffectiveEncoding.rawDescriptorRun_polynomial
#check EffectiveEncoding.rawExtraction_expression_budget
set_option pp.universes false in #print axioms EffectiveEncoding.rawExtraction_expression_budget
#check EffectiveEncoding.rawExtraction_expression_subtreeBound
set_option pp.universes false in #print axioms EffectiveEncoding.rawExtraction_expression_subtreeBound
#check EffectiveEncoding.rawExtraction_integerProgramRun_height
set_option pp.universes false in #print axioms EffectiveEncoding.rawExtraction_integerProgramRun_height
#check EffectiveEncoding.rawPacketCache_value
set_option pp.universes false in #print axioms EffectiveEncoding.rawPacketCache_value
#check EffectiveEncoding.rawPacketCache_expression_value
set_option pp.universes false in #print axioms EffectiveEncoding.rawPacketCache_expression_value
#check EffectiveEncoding.rawCachedIntegerRun_word
set_option pp.universes false in #print axioms EffectiveEncoding.rawCachedIntegerRun_word
#check EffectiveEncoding.rawDescriptorRun_word
set_option pp.universes false in #print axioms EffectiveEncoding.rawDescriptorRun_word
#check EffectiveEncoding.rawExtractionCode_eq
set_option pp.universes false in #print axioms EffectiveEncoding.rawExtractionCode_eq
#check EffectiveEncoding.rawExtractionCode_uses
set_option pp.universes false in #print axioms EffectiveEncoding.rawExtractionCode_uses
#check EffectiveEncoding.rawExtractionCode_length
set_option pp.universes false in #print axioms EffectiveEncoding.rawExtractionCode_length
#check EffectiveEncoding.rawExtractionCode_error
set_option pp.universes false in #print axioms EffectiveEncoding.rawExtractionCode_error
#check EffectiveEncoding.rawExtractionCode_fidelity
set_option pp.universes false in #print axioms EffectiveEncoding.rawExtractionCode_fidelity
#check EffectiveEncoding.integerScalar_ext_value
set_option pp.universes false in #print axioms EffectiveEncoding.integerScalar_ext_value
#check EffectiveEncoding.integerLiteral_zero
set_option pp.universes false in #print axioms EffectiveEncoding.integerLiteral_zero
#check EffectiveEncoding.integerLiteral_one
set_option pp.universes false in #print axioms EffectiveEncoding.integerLiteral_one
#check EffectiveEncoding.integerLiteral_half
set_option pp.universes false in #print axioms EffectiveEncoding.integerLiteral_half
#check EffectiveEncoding.integerLiteral_halfInv
set_option pp.universes false in #print axioms EffectiveEncoding.integerLiteral_halfInv
#check EffectiveEncoding.integerRoot_congr_value
set_option pp.universes false in #print axioms EffectiveEncoding.integerRoot_congr_value
#check EffectiveEncoding.rawAtomCos_eq
set_option pp.universes false in #print axioms EffectiveEncoding.rawAtomCos_eq
#check EffectiveEncoding.rawAtomSin_eq
set_option pp.universes false in #print axioms EffectiveEncoding.rawAtomSin_eq
#check EffectiveEncoding.rawHalfCos_eq
set_option pp.universes false in #print axioms EffectiveEncoding.rawHalfCos_eq
#check EffectiveEncoding.rawHalfSin_eq
set_option pp.universes false in #print axioms EffectiveEncoding.rawHalfSin_eq
#check EffectiveEncoding.AngleCode.rawCos_eq
set_option pp.universes false in #print axioms EffectiveEncoding.AngleCode.rawCos_eq
#check EffectiveEncoding.AngleCode.rawSin_eq
set_option pp.universes false in #print axioms EffectiveEncoding.AngleCode.rawSin_eq
#check EffectiveEncoding.rawPhaseCos_eq
set_option pp.universes false in #print axioms EffectiveEncoding.rawPhaseCos_eq
#check EffectiveEncoding.rawPhaseSin_eq
set_option pp.universes false in #print axioms EffectiveEncoding.rawPhaseSin_eq
#check EffectiveEncoding.SingleCode.rawPacket_eq
set_option pp.universes false in #print axioms EffectiveEncoding.SingleCode.rawPacket_eq
#check EffectiveEncoding.SingleCode.rawPacket_value
set_option pp.universes false in #print axioms EffectiveEncoding.SingleCode.rawPacket_value
#check EffectiveEncoding.extractionCode_rawPacket_height
set_option pp.universes false in #print axioms EffectiveEncoding.extractionCode_rawPacket_height
#check EffectiveEncoding.integerFraction_height
set_option pp.universes false in #print axioms EffectiveEncoding.integerFraction_height
#check EffectiveEncoding.AngleAtom.rawExpression_operations
set_option pp.universes false in #print axioms EffectiveEncoding.AngleAtom.rawExpression_operations
#check EffectiveEncoding.AngleCode.rawExpression_operations
set_option pp.universes false in #print axioms EffectiveEncoding.AngleCode.rawExpression_operations
#check EffectiveEncoding.SingleCode.rawPacketExpression_operations
set_option pp.universes false in #print axioms EffectiveEncoding.SingleCode.rawPacketExpression_operations
#check EffectiveEncoding.AngleAtom.rawExpression_budget
set_option pp.universes false in #print axioms EffectiveEncoding.AngleAtom.rawExpression_budget
#check EffectiveEncoding.AngleCode.rawExpression_budget
set_option pp.universes false in #print axioms EffectiveEncoding.AngleCode.rawExpression_budget
#check EffectiveEncoding.SingleCode.rawPacketExpression_budget
set_option pp.universes false in #print axioms EffectiveEncoding.SingleCode.rawPacketExpression_budget
#check EffectiveEncoding.rawProviderHeightBudget_le
set_option pp.universes false in #print axioms EffectiveEncoding.rawProviderHeightBudget_le
#check EffectiveEncoding.extractionCode_rawProviderExpression_budget
set_option pp.universes false in #print axioms EffectiveEncoding.extractionCode_rawProviderExpression_budget
#check EffectiveEncoding.extractionCode_rawProviderExpression_operations
set_option pp.universes false in #print axioms EffectiveEncoding.extractionCode_rawProviderExpression_operations
#check EffectiveEncoding.extractionCode_rawPacketProgram_rootCharge
set_option pp.universes false in #print axioms EffectiveEncoding.extractionCode_rawPacketProgram_rootCharge
#check EffectiveEncoding.extractionCode_rawProviderExpression_subtreeBound
set_option pp.universes false in #print axioms EffectiveEncoding.extractionCode_rawProviderExpression_subtreeBound
#check EffectiveEncoding.rawProviderBinaryExponent
set_option pp.universes false in #print axioms EffectiveEncoding.rawProviderBinaryExponent
#check EffectiveEncoding.extractionCode_rawProviderExpression_binaryProgramOperandTrace_height
set_option pp.universes false in #print axioms EffectiveEncoding.extractionCode_rawProviderExpression_binaryProgramOperandTrace_height
#check EffectiveEncoding.rawProviderRootBudget_mono
set_option pp.universes false in #print axioms EffectiveEncoding.rawProviderRootBudget_mono
#check EffectiveEncoding.rawTargetProgramCacheCharge_bound
set_option pp.universes false in #print axioms EffectiveEncoding.rawTargetProgramCacheCharge_bound
#check EffectiveEncoding.rawProviderCacheRoot_algebra
set_option pp.universes false in #print axioms EffectiveEncoding.rawProviderCacheRoot_algebra
#check EffectiveEncoding.rawTargetProgramCacheCharge_polynomial
set_option pp.universes false in #print axioms EffectiveEncoding.rawTargetProgramCacheCharge_polynomial
#check EffectiveEncoding.rawProviderCoefficient_algebra
set_option pp.universes false in #print axioms EffectiveEncoding.rawProviderCoefficient_algebra
#check EffectiveEncoding.rawProviderCacheRootCoefficient_polynomial
set_option pp.universes false in #print axioms EffectiveEncoding.rawProviderCacheRootCoefficient_polynomial
#check EffectiveEncoding.rawTargetProgramCacheCharge_polynomial_kq
set_option pp.universes false in #print axioms EffectiveEncoding.rawTargetProgramCacheCharge_polynomial_kq
#check EffectiveEncoding.AngleAtom.rawCosExpression_run
set_option pp.universes false in #print axioms EffectiveEncoding.AngleAtom.rawCosExpression_run
#check EffectiveEncoding.AngleAtom.rawSinExpression_run
set_option pp.universes false in #print axioms EffectiveEncoding.AngleAtom.rawSinExpression_run
#check EffectiveEncoding.AngleCode.rawCosExpression_run
set_option pp.universes false in #print axioms EffectiveEncoding.AngleCode.rawCosExpression_run
#check EffectiveEncoding.AngleCode.rawSinExpression_run
set_option pp.universes false in #print axioms EffectiveEncoding.AngleCode.rawSinExpression_run
#check EffectiveEncoding.rawPhaseCosExpression_run
set_option pp.universes false in #print axioms EffectiveEncoding.rawPhaseCosExpression_run
#check EffectiveEncoding.rawPhaseSinExpression_run
set_option pp.universes false in #print axioms EffectiveEncoding.rawPhaseSinExpression_run
#check EffectiveEncoding.SingleCode.rawPacketExpression_run
set_option pp.universes false in #print axioms EffectiveEncoding.SingleCode.rawPacketExpression_run
#check EffectiveEncoding.SingleCode.rawPacketProgram_value
set_option pp.universes false in #print axioms EffectiveEncoding.SingleCode.rawPacketProgram_value
#check EffectiveEncoding.sharedRawCachedRun_eq
set_option pp.universes false in #print axioms EffectiveEncoding.sharedRawCachedRun_eq
#check EffectiveEncoding.sharedRawDescriptorRun_eq
set_option pp.universes false in #print axioms EffectiveEncoding.sharedRawDescriptorRun_eq
#check EffectiveEncoding.sharedRawExtractionCode_eq
set_option pp.universes false in #print axioms EffectiveEncoding.sharedRawExtractionCode_eq
#check EffectiveEncoding.sharedRawExtractionCode_length
set_option pp.universes false in #print axioms EffectiveEncoding.sharedRawExtractionCode_length
#check EffectiveEncoding.sharedRawExtractionCode_error
set_option pp.universes false in #print axioms EffectiveEncoding.sharedRawExtractionCode_error
#check EffectiveEncoding.sharedRawExtractionCode_fidelity
set_option pp.universes false in #print axioms EffectiveEncoding.sharedRawExtractionCode_fidelity
#check EffectiveEncoding.sharedRawDescriptorRun_rootCharge
set_option pp.universes false in #print axioms EffectiveEncoding.sharedRawDescriptorRun_rootCharge
#check EffectiveEncoding.sharedRawDescriptorRun_integerBitBudget
set_option pp.universes false in #print axioms EffectiveEncoding.sharedRawDescriptorRun_integerBitBudget
#check EffectiveEncoding.extractionSharedRawRootCharge_eq
set_option pp.universes false in #print axioms EffectiveEncoding.extractionSharedRawRootCharge_eq
#check EffectiveEncoding.extractionSharedRawRootCharge_bound
set_option pp.universes false in #print axioms EffectiveEncoding.extractionSharedRawRootCharge_bound
#check EffectiveEncoding.applyStoredSwaps_value
set_option pp.universes false in #print axioms EffectiveEncoding.applyStoredSwaps_value
#check EffectiveEncoding.applyStoredSwaps_count
set_option pp.universes false in #print axioms EffectiveEncoding.applyStoredSwaps_count
#check EffectiveEncoding.storedAlignmentRun_word
set_option pp.universes false in #print axioms EffectiveEncoding.storedAlignmentRun_word
#check EffectiveEncoding.storedAlignmentRun_count
set_option pp.universes false in #print axioms EffectiveEncoding.storedAlignmentRun_count
#check EffectiveEncoding.storedAlignmentRun_empty_word
set_option pp.universes false in #print axioms EffectiveEncoding.storedAlignmentRun_empty_word
#check EffectiveEncoding.storedAlignmentRun_empty_count_bound
set_option pp.universes false in #print axioms EffectiveEncoding.storedAlignmentRun_empty_count_bound
#check EffectiveEncoding.storedOccupationStepCode_eq
set_option pp.universes false in #print axioms EffectiveEncoding.storedOccupationStepCode_eq
#check EffectiveEncoding.storedStageCode_eq
set_option pp.universes false in #print axioms EffectiveEncoding.storedStageCode_eq
#check EffectiveEncoding.storedCompressionCode_eq
set_option pp.universes false in #print axioms EffectiveEncoding.storedCompressionCode_eq
#check EffectiveEncoding.storedExtractionCode_eq
set_option pp.universes false in #print axioms EffectiveEncoding.storedExtractionCode_eq
#check EffectiveEncoding.storedSharedRawExtractionCode_eq
set_option pp.universes false in #print axioms EffectiveEncoding.storedSharedRawExtractionCode_eq
#check EffectiveEncoding.storedSharedRawExtractionCode_fidelity
set_option pp.universes false in #print axioms EffectiveEncoding.storedSharedRawExtractionCode_fidelity
#check EffectiveEncoding.stageStoredSwapApplications_exact
set_option pp.universes false in #print axioms EffectiveEncoding.stageStoredSwapApplications_exact
#check EffectiveEncoding.stageStoredSwapApplications_bound
set_option pp.universes false in #print axioms EffectiveEncoding.stageStoredSwapApplications_bound
#check EffectiveEncoding.extractionStoredSwapApplications_bound
set_option pp.universes false in #print axioms EffectiveEncoding.extractionStoredSwapApplications_bound
#check CircuitRecursion.binaryDivDigits_invariant
set_option pp.universes false in #print axioms CircuitRecursion.binaryDivDigits_invariant
#check CircuitRecursion.binaryDivDigits_correct
set_option pp.universes false in #print axioms CircuitRecursion.binaryDivDigits_correct
#check CircuitRecursion.binaryIntegerDiv_input_fuel
set_option pp.universes false in #print axioms CircuitRecursion.binaryIntegerDiv_input_fuel
#check CircuitRecursion.binaryIntegerDivMod_eq
set_option pp.universes false in #print axioms CircuitRecursion.binaryIntegerDivMod_eq
#check CircuitRecursion.binaryIntegerDiv_eq
set_option pp.universes false in #print axioms CircuitRecursion.binaryIntegerDiv_eq
#check CircuitRecursion.binaryIntegerMod_eq
set_option pp.universes false in #print axioms CircuitRecursion.binaryIntegerMod_eq
#check CircuitRecursion.binaryIntegerDiv_operations
set_option pp.universes false in #print axioms CircuitRecursion.binaryIntegerDiv_operations
#check CircuitRecursion.binaryDivOperandTrace_height
set_option pp.universes false in #print axioms CircuitRecursion.binaryDivOperandTrace_height
#check CircuitRecursion.binarySqrtDigits_correct
set_option pp.universes false in #print axioms CircuitRecursion.binarySqrtDigits_correct
#check CircuitRecursion.binarySqrtDigits_le_input
set_option pp.universes false in #print axioms CircuitRecursion.binarySqrtDigits_le_input
#check CircuitRecursion.binaryIntegerSqrt_eq
set_option pp.universes false in #print axioms CircuitRecursion.binaryIntegerSqrt_eq
#check CircuitRecursion.binaryIntegerSqrtFuel_bound
set_option pp.universes false in #print axioms CircuitRecursion.binaryIntegerSqrtFuel_bound
#check CircuitRecursion.binarySqrtDigitOperations_eq
set_option pp.universes false in #print axioms CircuitRecursion.binarySqrtDigitOperations_eq
#check CircuitRecursion.binaryIntegerSqrt_operations
set_option pp.universes false in #print axioms CircuitRecursion.binaryIntegerSqrt_operations
#check CircuitRecursion.binarySqrtOperandTrace_height
set_option pp.universes false in #print axioms CircuitRecursion.binarySqrtOperandTrace_height
#check CircuitRecursion.binaryIntegerSqrt_operandTrace_height
set_option pp.universes false in #print axioms CircuitRecursion.binaryIntegerSqrt_operandTrace_height
#check CircuitRecursion.ScalarExpression.binaryProgramOperandTrace_height
set_option pp.universes false in #print axioms CircuitRecursion.ScalarExpression.binaryProgramOperandTrace_height
#check CircuitRecursion.PacketExpression.binaryProgramOperandTrace_height
set_option pp.universes false in #print axioms CircuitRecursion.PacketExpression.binaryProgramOperandTrace_height
#check CircuitRecursion.ArithmeticWordResult.binaryProgramOperandTrace_height
set_option pp.universes false in #print axioms CircuitRecursion.ArithmeticWordResult.binaryProgramOperandTrace_height
#check CircuitRecursion.cachedArithmeticRun_binaryProgramOperandTrace_height
set_option pp.universes false in #print axioms CircuitRecursion.cachedArithmeticRun_binaryProgramOperandTrace_height
#check CircuitRecursion.cachedArithmeticRun_rational_binaryProgramOperandTrace_height
set_option pp.universes false in #print axioms CircuitRecursion.cachedArithmeticRun_rational_binaryProgramOperandTrace_height
#check CircuitRecursion.IntegerScalar.binaryRoot_eq
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalar.binaryRoot_eq
#check CircuitRecursion.IntegerScalar.binaryRoot_operations
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalar.binaryRoot_operations
#check CircuitRecursion.IntegerScalar.binaryRoot_operandTrace_height
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalar.binaryRoot_operandTrace_height
#check CircuitRecursion.ScalarExpression.binaryRootRun_eq
set_option pp.universes false in #print axioms CircuitRecursion.ScalarExpression.binaryRootRun_eq
#check CircuitRecursion.PacketExpression.binaryRootRun_eq
set_option pp.universes false in #print axioms CircuitRecursion.PacketExpression.binaryRootRun_eq
#check CircuitRecursion.ScalarExpression.binaryRootRun_correct
set_option pp.universes false in #print axioms CircuitRecursion.ScalarExpression.binaryRootRun_correct
#check CircuitRecursion.PacketExpression.binaryRootRun_correct
set_option pp.universes false in #print axioms CircuitRecursion.PacketExpression.binaryRootRun_correct
#check CircuitRecursion.IntegerScalar.binaryRootPrimitiveOperations_bound
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalar.binaryRootPrimitiveOperations_bound
#check CircuitRecursion.IntegerScalar.binaryRootOperandTrace_bound
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalar.binaryRootOperandTrace_bound
#check CircuitRecursion.IntegerScalar.binaryRootOperandTrace_binaryLength
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalar.binaryRootOperandTrace_binaryLength
#check CircuitRecursion.ScalarExpression.binaryRootRun_height
set_option pp.universes false in #print axioms CircuitRecursion.ScalarExpression.binaryRootRun_height
#check CircuitRecursion.PacketExpression.binaryRootRun_height
set_option pp.universes false in #print axioms CircuitRecursion.PacketExpression.binaryRootRun_height
#check CircuitRecursion.pairTraceT_pos
set_option pp.universes false in #print axioms CircuitRecursion.pairTraceT_pos
#check CircuitRecursion.pairTraceT_bound
set_option pp.universes false in #print axioms CircuitRecursion.pairTraceT_bound
#check CircuitRecursion.numericalThreshold_pow_bound
set_option pp.universes false in #print axioms CircuitRecursion.numericalThreshold_pow_bound
#check CircuitRecursion.traceT_threshold_bound
set_option pp.universes false in #print axioms CircuitRecursion.traceT_threshold_bound
#check CircuitRecursion.pairedTraceS_step
set_option pp.universes false in #print axioms CircuitRecursion.pairedTraceS_step
#check CircuitRecursion.pairTraceS_bound
set_option pp.universes false in #print axioms CircuitRecursion.pairTraceS_bound
#check CircuitRecursion.pairedTraceR_step
set_option pp.universes false in #print axioms CircuitRecursion.pairedTraceR_step
#check CircuitRecursion.mul_extra_scale
set_option pp.universes false in #print axioms CircuitRecursion.mul_extra_scale
#check CircuitRecursion.pairTraceR_bound
set_option pp.universes false in #print axioms CircuitRecursion.pairTraceR_bound
#check CircuitRecursion.traceRGrowth_precision_bound
set_option pp.universes false in #print axioms CircuitRecursion.traceRGrowth_precision_bound
#check CircuitRecursion.tracedPairWord_flat_integerBitBudget
set_option pp.universes false in #print axioms CircuitRecursion.tracedPairWord_flat_integerBitBudget
#check CircuitRecursion.cachedIntegerBudget_algebra
set_option pp.universes false in #print axioms CircuitRecursion.cachedIntegerBudget_algebra
#check CircuitRecursion.cachedArithmeticRun_eq_packetExpression
set_option pp.universes false in #print axioms CircuitRecursion.cachedArithmeticRun_eq_packetExpression
#check CircuitRecursion.cachedArithmeticRun_integerBitBudget
set_option pp.universes false in #print axioms CircuitRecursion.cachedArithmeticRun_integerBitBudget
#check CircuitRecursion.ArithmeticWordResult.expression_integerHeight
set_option pp.universes false in #print axioms CircuitRecursion.ArithmeticWordResult.expression_integerHeight
#check CircuitRecursion.cachedArithmeticRun_expression_integerHeight
set_option pp.universes false in #print axioms CircuitRecursion.cachedArithmeticRun_expression_integerHeight
#check CircuitRecursion.ScalarExpression.costedIntegerRun_value
set_option pp.universes false in #print axioms CircuitRecursion.ScalarExpression.costedIntegerRun_value
#check CircuitRecursion.PacketExpression.costedIntegerRun_value
set_option pp.universes false in #print axioms CircuitRecursion.PacketExpression.costedIntegerRun_value
#check CircuitRecursion.ScalarExpression.costedIntegerRun_rootCharge
set_option pp.universes false in #print axioms CircuitRecursion.ScalarExpression.costedIntegerRun_rootCharge
#check CircuitRecursion.PacketExpression.costedIntegerRun_rootCharge
set_option pp.universes false in #print axioms CircuitRecursion.PacketExpression.costedIntegerRun_rootCharge
#check CircuitRecursion.ScalarExpression.costedIntegerRun_correct
set_option pp.universes false in #print axioms CircuitRecursion.ScalarExpression.costedIntegerRun_correct
#check CircuitRecursion.PacketExpression.costedIntegerRun_correct
set_option pp.universes false in #print axioms CircuitRecursion.PacketExpression.costedIntegerRun_correct
#check CircuitRecursion.costedTracedBase_result
set_option pp.universes false in #print axioms CircuitRecursion.costedTracedBase_result
#check CircuitRecursion.costedTracedBase_rootCharge
set_option pp.universes false in #print axioms CircuitRecursion.costedTracedBase_rootCharge
#check CircuitRecursion.costedTracedCorrection_result
set_option pp.universes false in #print axioms CircuitRecursion.costedTracedCorrection_result
#check CircuitRecursion.costedTracedCorrection_rootCharge
set_option pp.universes false in #print axioms CircuitRecursion.costedTracedCorrection_rootCharge
#check CircuitRecursion.costedTracedPairWord_result
set_option pp.universes false in #print axioms CircuitRecursion.costedTracedPairWord_result
#check CircuitRecursion.costedTracedPairWord_rootCharge
set_option pp.universes false in #print axioms CircuitRecursion.costedTracedPairWord_rootCharge
#check CircuitRecursion.costedCachedArithmeticRun_result
set_option pp.universes false in #print axioms CircuitRecursion.costedCachedArithmeticRun_result
#check CircuitRecursion.costedCachedArithmeticRun_rootCharge
set_option pp.universes false in #print axioms CircuitRecursion.costedCachedArithmeticRun_rootCharge
#check CircuitRecursion.ScalarExpression.integerProgramRun_eq
set_option pp.universes false in #print axioms CircuitRecursion.ScalarExpression.integerProgramRun_eq
#check CircuitRecursion.PacketExpression.integerProgramRun_eq
set_option pp.universes false in #print axioms CircuitRecursion.PacketExpression.integerProgramRun_eq
#check CircuitRecursion.ScalarExpression.integerProgramRun_correct
set_option pp.universes false in #print axioms CircuitRecursion.ScalarExpression.integerProgramRun_correct
#check CircuitRecursion.PacketExpression.integerProgramRun_correct
set_option pp.universes false in #print axioms CircuitRecursion.PacketExpression.integerProgramRun_correct
#check CircuitRecursion.integerTracedBase_eq
set_option pp.universes false in #print axioms CircuitRecursion.integerTracedBase_eq
#check CircuitRecursion.integerTracedCorrection_eq
set_option pp.universes false in #print axioms CircuitRecursion.integerTracedCorrection_eq
#check CircuitRecursion.integerTracedCorrection_function
set_option pp.universes false in #print axioms CircuitRecursion.integerTracedCorrection_function
#check CircuitRecursion.integerTracedPairWord_eq
set_option pp.universes false in #print axioms CircuitRecursion.integerTracedPairWord_eq
#check CircuitRecursion.integerCachedArithmeticRun_eq
set_option pp.universes false in #print axioms CircuitRecursion.integerCachedArithmeticRun_eq
#check CircuitRecursion.integerCachedArithmeticRun_rational_integerBitBudget
set_option pp.universes false in #print axioms CircuitRecursion.integerCachedArithmeticRun_rational_integerBitBudget
#check CircuitRecursion.integerCachedArithmeticSU2Synthesis
set_option pp.universes false in #print axioms CircuitRecursion.integerCachedArithmeticSU2Synthesis
#check CircuitRecursion.IntegerScalar.crossLE_value
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalar.crossLE_value
#check CircuitRecursion.integerMinIndex_eq
set_option pp.universes false in #print axioms CircuitRecursion.integerMinIndex_eq
#check CircuitRecursion.integerMaxIndex_eq
set_option pp.universes false in #print axioms CircuitRecursion.integerMaxIndex_eq
#check CircuitRecursion.IntegerScalar.crossLE_operands_height
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalar.crossLE_operands_height
#check CircuitRecursion.ScalarExpression.integerSubtreeBound
set_option pp.universes false in #print axioms CircuitRecursion.ScalarExpression.integerSubtreeBound
#check CircuitRecursion.PacketExpression.integerSubtreeBound
set_option pp.universes false in #print axioms CircuitRecursion.PacketExpression.integerSubtreeBound
#check CircuitRecursion.ArithmeticWordResult.expression_integerSubtreeBound
set_option pp.universes false in #print axioms CircuitRecursion.ArithmeticWordResult.expression_integerSubtreeBound
#check CircuitRecursion.cachedArithmeticRun_expression_integerSubtreeBound
set_option pp.universes false in #print axioms CircuitRecursion.cachedArithmeticRun_expression_integerSubtreeBound
#check CircuitRecursion.bitFactorEnvelope_closed
set_option pp.universes false in #print axioms CircuitRecursion.bitFactorEnvelope_closed
#check CircuitRecursion.tracedBase_integerBitBudget
set_option pp.universes false in #print axioms CircuitRecursion.tracedBase_integerBitBudget
#check CircuitRecursion.tracedCorrection_integerBitBudget
set_option pp.universes false in #print axioms CircuitRecursion.tracedCorrection_integerBitBudget
#check CircuitRecursion.tracedPairWord_integerBitBudget
set_option pp.universes false in #print axioms CircuitRecursion.tracedPairWord_integerBitBudget
#check CircuitRecursion.cachedRationalPacketExpression_bitEnvelope
set_option pp.universes false in #print axioms CircuitRecursion.cachedRationalPacketExpression_bitEnvelope
#check CircuitRecursion.cachedArithmeticRun_eq_rationalPacketExpression
set_option pp.universes false in #print axioms CircuitRecursion.cachedArithmeticRun_eq_rationalPacketExpression
#check CircuitRecursion.cachedArithmeticRun_envelope_integerBitBudget
set_option pp.universes false in #print axioms CircuitRecursion.cachedArithmeticRun_envelope_integerBitBudget
#check CircuitRecursion.cachedArithmeticRun_rational_integerBitBudget
set_option pp.universes false in #print axioms CircuitRecursion.cachedArithmeticRun_rational_integerBitBudget
#check CircuitRecursion.cachedArithmeticRun_rational_expression_integerSubtreeBound
set_option pp.universes false in #print axioms CircuitRecursion.cachedArithmeticRun_rational_expression_integerSubtreeBound
#check CircuitRecursion.IntegerScalar.ofRat_intCast
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalar.ofRat_intCast
#check CircuitRecursion.IntegerScalar.ofInt_positive_inv
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalar.ofInt_positive_inv
#check CircuitRecursion.rawScalarExpression_integerProgramRun
set_option pp.universes false in #print axioms CircuitRecursion.rawScalarExpression_integerProgramRun
#check CircuitRecursion.rawPacketExpression_integerProgramRun
set_option pp.universes false in #print axioms CircuitRecursion.rawPacketExpression_integerProgramRun
#check CircuitRecursion.rawPacketExpression_eval
set_option pp.universes false in #print axioms CircuitRecursion.rawPacketExpression_eval
#check CircuitRecursion.rawScalarExpression_operations
set_option pp.universes false in #print axioms CircuitRecursion.rawScalarExpression_operations
#check CircuitRecursion.rawPacketExpression_operations
set_option pp.universes false in #print axioms CircuitRecursion.rawPacketExpression_operations
#check CircuitRecursion.rationalBinaryExponent_intCast_le
set_option pp.universes false in #print axioms CircuitRecursion.rationalBinaryExponent_intCast_le
#check CircuitRecursion.rawScalarExpression_integerBitBudget
set_option pp.universes false in #print axioms CircuitRecursion.rawScalarExpression_integerBitBudget
#check CircuitRecursion.rawPacketExpression_integerBitBudget
set_option pp.universes false in #print axioms CircuitRecursion.rawPacketExpression_integerBitBudget
#check CircuitRecursion.rawPacketExpression_integerProgramRun_height
set_option pp.universes false in #print axioms CircuitRecursion.rawPacketExpression_integerProgramRun_height
#check CircuitRecursion.rawPacketExpressionOracle_eval
set_option pp.universes false in #print axioms CircuitRecursion.rawPacketExpressionOracle_eval
#check CircuitRecursion.rawPacketExpressionOracle_bitEnvelope
set_option pp.universes false in #print axioms CircuitRecursion.rawPacketExpressionOracle_bitEnvelope
#check CircuitRecursion.rawCorrectionOperationOffset_le
set_option pp.universes false in #print axioms CircuitRecursion.rawCorrectionOperationOffset_le
#check CircuitRecursion.rawPairOperationOffset_le
set_option pp.universes false in #print axioms CircuitRecursion.rawPairOperationOffset_le
#check CircuitRecursion.tracedPairWord_twenty_operations
set_option pp.universes false in #print axioms CircuitRecursion.tracedPairWord_twenty_operations
#check CircuitRecursion.tracedPairWord_twenty_precision_operations
set_option pp.universes false in #print axioms CircuitRecursion.tracedPairWord_twenty_precision_operations
#check CircuitRecursion.rawPacketExpressionOracle_operationBound
set_option pp.universes false in #print axioms CircuitRecursion.rawPacketExpressionOracle_operationBound
#check CircuitRecursion.costedRawPacketPairWord_operations
set_option pp.universes false in #print axioms CircuitRecursion.costedRawPacketPairWord_operations
#check CircuitRecursion.costedTracedPairWord_twenty_rootCharge
set_option pp.universes false in #print axioms CircuitRecursion.costedTracedPairWord_twenty_rootCharge
#check CircuitRecursion.rawExpressionWord_bound
set_option pp.universes false in #print axioms CircuitRecursion.rawExpressionWord_bound
#check CircuitRecursion.rawTracedBase_operations
set_option pp.universes false in #print axioms CircuitRecursion.rawTracedBase_operations
#check CircuitRecursion.rawTracedCorrection_operations
set_option pp.universes false in #print axioms CircuitRecursion.rawTracedCorrection_operations
#check CircuitRecursion.rawTracedPairWord_operations
set_option pp.universes false in #print axioms CircuitRecursion.rawTracedPairWord_operations
#check CircuitRecursion.natural_le_power_two
set_option pp.universes false in #print axioms CircuitRecursion.natural_le_power_two
#check CircuitRecursion.IntegerScalar.rootOperandTrace_height
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalar.rootOperandTrace_height
#check CircuitRecursion.integerStoppingThresholdOperandTrace_height
set_option pp.universes false in #print axioms CircuitRecursion.integerStoppingThresholdOperandTrace_height
#check CircuitRecursion.IntegerScalar.rootOperandTrace_binaryLength
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalar.rootOperandTrace_binaryLength
#check CircuitRecursion.IntegerScalar.root_numerator_in_operandTrace
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalar.root_numerator_in_operandTrace
#check CircuitRecursion.IntegerScalar.root_denominator_in_operandTrace
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalar.root_denominator_in_operandTrace
#check CircuitRecursion.ScalarExpression.binaryRootPrimitiveOperations_bound
set_option pp.universes false in #print axioms CircuitRecursion.ScalarExpression.binaryRootPrimitiveOperations_bound
#check CircuitRecursion.PacketExpression.binaryRootPrimitiveOperations_bound
set_option pp.universes false in #print axioms CircuitRecursion.PacketExpression.binaryRootPrimitiveOperations_bound
#check CircuitRecursion.ArithmeticWordResult.binaryRootPrimitiveOperations_bound
set_option pp.universes false in #print axioms CircuitRecursion.ArithmeticWordResult.binaryRootPrimitiveOperations_bound
#check CircuitRecursion.cachedArithmeticRun_binaryRootPrimitiveOperations
set_option pp.universes false in #print axioms CircuitRecursion.cachedArithmeticRun_binaryRootPrimitiveOperations
#check CircuitRecursion.cachedArithmeticRun_envelope_binaryRootPrimitiveOperations
set_option pp.universes false in #print axioms CircuitRecursion.cachedArithmeticRun_envelope_binaryRootPrimitiveOperations
#check CircuitRecursion.cachedRootCost_algebra
set_option pp.universes false in #print axioms CircuitRecursion.cachedRootCost_algebra
#check CircuitRecursion.cachedArithmeticRun_binaryRootPrimitiveOperations_polynomial
set_option pp.universes false in #print axioms CircuitRecursion.cachedArithmeticRun_binaryRootPrimitiveOperations_polynomial
#check CircuitRecursion.ScalarExpression.rootOperandTrace_height
set_option pp.universes false in #print axioms CircuitRecursion.ScalarExpression.rootOperandTrace_height
#check CircuitRecursion.PacketExpression.rootOperandTrace_height
set_option pp.universes false in #print axioms CircuitRecursion.PacketExpression.rootOperandTrace_height
#check CircuitRecursion.ArithmeticWordResult.rootOperandTrace_height
set_option pp.universes false in #print axioms CircuitRecursion.ArithmeticWordResult.rootOperandTrace_height
#check CircuitRecursion.cachedArithmeticRun_rootOperandTrace_height
set_option pp.universes false in #print axioms CircuitRecursion.cachedArithmeticRun_rootOperandTrace_height
#check CircuitRecursion.cachedArithmeticRun_rational_rootOperandTrace_height
set_option pp.universes false in #print axioms CircuitRecursion.cachedArithmeticRun_rational_rootOperandTrace_height
#check CircuitRecursion.IntegerScalar.sharedBinaryRoot_quotient
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalar.sharedBinaryRoot_quotient
#check CircuitRecursion.IntegerScalar.sharedBinaryRoot_value
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalar.sharedBinaryRoot_value
#check CircuitRecursion.IntegerScalar.sharedBinaryRoot_charge
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalar.sharedBinaryRoot_charge
#check CircuitRecursion.IntegerScalar.sharedBinaryRoot_eq
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalar.sharedBinaryRoot_eq
#check CircuitRecursion.IntegerScalar.sharedBinaryRoot_correct
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalar.sharedBinaryRoot_correct
#check CircuitRecursion.IntegerScalar.sharedBinaryRoot_height
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalar.sharedBinaryRoot_height
#check CircuitRecursion.IntegerScalar.sharedBinaryRoot_charge_bound
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalar.sharedBinaryRoot_charge_bound
#check CircuitRecursion.ScalarExpression.sharedCostedIntegerRun_eq
set_option pp.universes false in #print axioms CircuitRecursion.ScalarExpression.sharedCostedIntegerRun_eq
#check CircuitRecursion.PacketExpression.sharedCostedIntegerRun_eq
set_option pp.universes false in #print axioms CircuitRecursion.PacketExpression.sharedCostedIntegerRun_eq
#check CircuitRecursion.sharedCostedTracedBase_eq
set_option pp.universes false in #print axioms CircuitRecursion.sharedCostedTracedBase_eq
#check CircuitRecursion.sharedCostedTracedCorrection_eq
set_option pp.universes false in #print axioms CircuitRecursion.sharedCostedTracedCorrection_eq
#check CircuitRecursion.sharedCostedTracedPairWord_eq
set_option pp.universes false in #print axioms CircuitRecursion.sharedCostedTracedPairWord_eq
#check CircuitRecursion.sharedCostedCachedArithmeticRun_eq
set_option pp.universes false in #print axioms CircuitRecursion.sharedCostedCachedArithmeticRun_eq
#check CircuitRecursion.ScalarExpression.sharedCostedIntegerRun_value
set_option pp.universes false in #print axioms CircuitRecursion.ScalarExpression.sharedCostedIntegerRun_value
#check CircuitRecursion.PacketExpression.sharedCostedIntegerRun_value
set_option pp.universes false in #print axioms CircuitRecursion.PacketExpression.sharedCostedIntegerRun_value
#check CircuitRecursion.ScalarExpression.sharedCostedIntegerRun_rootCharge
set_option pp.universes false in #print axioms CircuitRecursion.ScalarExpression.sharedCostedIntegerRun_rootCharge
#check CircuitRecursion.PacketExpression.sharedCostedIntegerRun_rootCharge
set_option pp.universes false in #print axioms CircuitRecursion.PacketExpression.sharedCostedIntegerRun_rootCharge
#check CircuitRecursion.ScalarExpression.sharedCostedIntegerRun_correct
set_option pp.universes false in #print axioms CircuitRecursion.ScalarExpression.sharedCostedIntegerRun_correct
#check CircuitRecursion.PacketExpression.sharedCostedIntegerRun_correct
set_option pp.universes false in #print axioms CircuitRecursion.PacketExpression.sharedCostedIntegerRun_correct
#check CircuitRecursion.sharedCostedTracedBase_result
set_option pp.universes false in #print axioms CircuitRecursion.sharedCostedTracedBase_result
#check CircuitRecursion.sharedCostedTracedBase_rootCharge
set_option pp.universes false in #print axioms CircuitRecursion.sharedCostedTracedBase_rootCharge
#check CircuitRecursion.sharedCostedTracedCorrection_result
set_option pp.universes false in #print axioms CircuitRecursion.sharedCostedTracedCorrection_result
#check CircuitRecursion.sharedCostedTracedCorrection_rootCharge
set_option pp.universes false in #print axioms CircuitRecursion.sharedCostedTracedCorrection_rootCharge
#check CircuitRecursion.sharedCostedTracedPairWord_result
set_option pp.universes false in #print axioms CircuitRecursion.sharedCostedTracedPairWord_result
#check CircuitRecursion.sharedCostedTracedPairWord_rootCharge
set_option pp.universes false in #print axioms CircuitRecursion.sharedCostedTracedPairWord_rootCharge
#check CircuitRecursion.sharedCostedCachedArithmeticRun_result
set_option pp.universes false in #print axioms CircuitRecursion.sharedCostedCachedArithmeticRun_result
#check CircuitRecursion.sharedCostedCachedArithmeticRun_rootCharge
set_option pp.universes false in #print axioms CircuitRecursion.sharedCostedCachedArithmeticRun_rootCharge
#check EffectiveEncoding.actualRawRootCoefficient
set_option pp.universes false in #print axioms EffectiveEncoding.actualRawRootCoefficient
#check EffectiveEncoding.gateRawRootCharge
set_option pp.universes false in #print axioms EffectiveEncoding.gateRawRootCharge
#check EffectiveEncoding.extractionRawRootCharge
set_option pp.universes false in #print axioms EffectiveEncoding.extractionRawRootCharge
#check EffectiveEncoding.rawTargetProgramCache
set_option pp.universes false in #print axioms EffectiveEncoding.rawTargetProgramCache
#check EffectiveEncoding.targetProgramDescriptorRun
set_option pp.universes false in #print axioms EffectiveEncoding.targetProgramDescriptorRun
#check EffectiveEncoding.chargedProviderExtractionCode
set_option pp.universes false in #print axioms EffectiveEncoding.chargedProviderExtractionCode
#check EffectiveEncoding.gateProviderProgramRootCharge
set_option pp.universes false in #print axioms EffectiveEncoding.gateProviderProgramRootCharge
#check EffectiveEncoding.extractionProviderProgramRootCharge
set_option pp.universes false in #print axioms EffectiveEncoding.extractionProviderProgramRootCharge
#check EffectiveEncoding.costedRawCachedRun
set_option pp.universes false in #print axioms EffectiveEncoding.costedRawCachedRun
#check EffectiveEncoding.costedRawDescriptorRun
set_option pp.universes false in #print axioms EffectiveEncoding.costedRawDescriptorRun
#check EffectiveEncoding.costedRawExtractionCode
set_option pp.universes false in #print axioms EffectiveEncoding.costedRawExtractionCode
#check EffectiveEncoding.FieldRun
set_option pp.universes false in #print axioms EffectiveEncoding.FieldRun
#check EffectiveEncoding.FieldRun.empty
set_option pp.universes false in #print axioms EffectiveEncoding.FieldRun.empty
#check EffectiveEncoding.FieldRun.emit
set_option pp.universes false in #print axioms EffectiveEncoding.FieldRun.emit
#check EffectiveEncoding.FieldRun.append
set_option pp.universes false in #print axioms EffectiveEncoding.FieldRun.append
#check EffectiveEncoding.countedAngleFields
set_option pp.universes false in #print axioms EffectiveEncoding.countedAngleFields
#check EffectiveEncoding.countedSingleFields
set_option pp.universes false in #print axioms EffectiveEncoding.countedSingleFields
#check EffectiveEncoding.countedGateFields
set_option pp.universes false in #print axioms EffectiveEncoding.countedGateFields
#check EffectiveEncoding.countedWordFields
set_option pp.universes false in #print axioms EffectiveEncoding.countedWordFields
#check EffectiveEncoding.countedProgramFields
set_option pp.universes false in #print axioms EffectiveEncoding.countedProgramFields
#check EffectiveEncoding.AngleCode.fields
set_option pp.universes false in #print axioms EffectiveEncoding.AngleCode.fields
#check EffectiveEncoding.parseAngleFields
set_option pp.universes false in #print axioms EffectiveEncoding.parseAngleFields
#check EffectiveEncoding.SingleCode.fields
set_option pp.universes false in #print axioms EffectiveEncoding.SingleCode.fields
#check EffectiveEncoding.parseSingleFields
set_option pp.universes false in #print axioms EffectiveEncoding.parseSingleFields
#check EffectiveEncoding.GateCode.fields
set_option pp.universes false in #print axioms EffectiveEncoding.GateCode.fields
#check EffectiveEncoding.parseGateFields
set_option pp.universes false in #print axioms EffectiveEncoding.parseGateFields
#check EffectiveEncoding.wordFields
set_option pp.universes false in #print axioms EffectiveEncoding.wordFields
#check EffectiveEncoding.parseWordFields
set_option pp.universes false in #print axioms EffectiveEncoding.parseWordFields
#check EffectiveEncoding.programFields
set_option pp.universes false in #print axioms EffectiveEncoding.programFields
#check EffectiveEncoding.parseProgramFields
set_option pp.universes false in #print axioms EffectiveEncoding.parseProgramFields
#check EffectiveEncoding.logarithmicPrecision
set_option pp.universes false in #print axioms EffectiveEncoding.logarithmicPrecision
#check EffectiveEncoding.rawLogarithmicOperandBudget
set_option pp.universes false in #print axioms EffectiveEncoding.rawLogarithmicOperandBudget
#check EffectiveEncoding.constantExpression
set_option pp.universes false in #print axioms EffectiveEncoding.constantExpression
#check EffectiveEncoding.meanPlusExpression
set_option pp.universes false in #print axioms EffectiveEncoding.meanPlusExpression
#check EffectiveEncoding.halfCosExpression
set_option pp.universes false in #print axioms EffectiveEncoding.halfCosExpression
#check EffectiveEncoding.halfSinExpression
set_option pp.universes false in #print axioms EffectiveEncoding.halfSinExpression
#check EffectiveEncoding.AngleAtom.cosExpression
set_option pp.universes false in #print axioms EffectiveEncoding.AngleAtom.cosExpression
#check EffectiveEncoding.AngleAtom.sinExpression
set_option pp.universes false in #print axioms EffectiveEncoding.AngleAtom.sinExpression
#check EffectiveEncoding.AngleCode.cosExpression
set_option pp.universes false in #print axioms EffectiveEncoding.AngleCode.cosExpression
#check EffectiveEncoding.AngleCode.sinExpression
set_option pp.universes false in #print axioms EffectiveEncoding.AngleCode.sinExpression
#check EffectiveEncoding.phaseCosExpression
set_option pp.universes false in #print axioms EffectiveEncoding.phaseCosExpression
#check EffectiveEncoding.phaseSinExpression
set_option pp.universes false in #print axioms EffectiveEncoding.phaseSinExpression
#check EffectiveEncoding.SingleCode.packetExpression
set_option pp.universes false in #print axioms EffectiveEncoding.SingleCode.packetExpression
#check EffectiveEncoding.SingleCode.integerPacket
set_option pp.universes false in #print axioms EffectiveEncoding.SingleCode.integerPacket
#check EffectiveEncoding.halfExpressionBudget
set_option pp.universes false in #print axioms EffectiveEncoding.halfExpressionBudget
#check EffectiveEncoding.providerHeightBudget
set_option pp.universes false in #print axioms EffectiveEncoding.providerHeightBudget
#check EffectiveEncoding.scalarIntermediateHeights
set_option pp.universes false in #print axioms EffectiveEncoding.scalarIntermediateHeights
#check EffectiveEncoding.packetIntermediateHeights
set_option pp.universes false in #print axioms EffectiveEncoding.packetIntermediateHeights
#check EffectiveEncoding.fourMax
set_option pp.universes false in #print axioms EffectiveEncoding.fourMax
#check EffectiveEncoding.scalarRootPrecision
set_option pp.universes false in #print axioms EffectiveEncoding.scalarRootPrecision
#check EffectiveEncoding.packetRootPrecision
set_option pp.universes false in #print axioms EffectiveEncoding.packetRootPrecision
#check EffectiveEncoding.targetCacheOperations
set_option pp.universes false in #print axioms EffectiveEncoding.targetCacheOperations
#check EffectiveEncoding.gateTargetCacheOperations
set_option pp.universes false in #print axioms EffectiveEncoding.gateTargetCacheOperations
#check EffectiveEncoding.extractionTargetCacheOperations
set_option pp.universes false in #print axioms EffectiveEncoding.extractionTargetCacheOperations
#check EffectiveEncoding.integerTargetCache
set_option pp.universes false in #print axioms EffectiveEncoding.integerTargetCache
#check EffectiveEncoding.integerDescriptorSynthesis
set_option pp.universes false in #print axioms EffectiveEncoding.integerDescriptorSynthesis
#check EffectiveEncoding.integerNumericalExtractionCode
set_option pp.universes false in #print axioms EffectiveEncoding.integerNumericalExtractionCode
#check EffectiveEncoding.integerPacketBits
set_option pp.universes false in #print axioms EffectiveEncoding.integerPacketBits
#check EffectiveEncoding.integerTargetCacheBits
set_option pp.universes false in #print axioms EffectiveEncoding.integerTargetCacheBits
#check EffectiveEncoding.extractionWithTargetOperations
set_option pp.universes false in #print axioms EffectiveEncoding.extractionWithTargetOperations
#check EffectiveEncoding.actualTargetCacheHeight
set_option pp.universes false in #print axioms EffectiveEncoding.actualTargetCacheHeight
#check EffectiveEncoding.actualDescriptorTraceBudget
set_option pp.universes false in #print axioms EffectiveEncoding.actualDescriptorTraceBudget
#check EffectiveEncoding.actualTraceConstant
set_option pp.universes false in #print axioms EffectiveEncoding.actualTraceConstant
#check EffectiveEncoding.actualGatePolynomial
set_option pp.universes false in #print axioms EffectiveEncoding.actualGatePolynomial
#check EffectiveEncoding.pipelinePrecisionPolynomial
set_option pp.universes false in #print axioms EffectiveEncoding.pipelinePrecisionPolynomial
#check EffectiveEncoding.extractionOperandPolynomial
set_option pp.universes false in #print axioms EffectiveEncoding.extractionOperandPolynomial
#check EffectiveEncoding.buildRawPacketCache
set_option pp.universes false in #print axioms EffectiveEncoding.buildRawPacketCache
#check EffectiveEncoding.readRawPacketCache
set_option pp.universes false in #print axioms EffectiveEncoding.readRawPacketCache
#check EffectiveEncoding.rawCachedIntegerRun
set_option pp.universes false in #print axioms EffectiveEncoding.rawCachedIntegerRun
#check EffectiveEncoding.rawDescriptorRun
set_option pp.universes false in #print axioms EffectiveEncoding.rawDescriptorRun
#check EffectiveEncoding.rawExtractionCode
set_option pp.universes false in #print axioms EffectiveEncoding.rawExtractionCode
#check EffectiveEncoding.integerFraction
set_option pp.universes false in #print axioms EffectiveEncoding.integerFraction
#check EffectiveEncoding.integerHalf
set_option pp.universes false in #print axioms EffectiveEncoding.integerHalf
#check EffectiveEncoding.rawAtomCos
set_option pp.universes false in #print axioms EffectiveEncoding.rawAtomCos
#check EffectiveEncoding.rawAtomSin
set_option pp.universes false in #print axioms EffectiveEncoding.rawAtomSin
#check EffectiveEncoding.RawScalarOracle
set_option pp.universes false in #print axioms EffectiveEncoding.RawScalarOracle
#check EffectiveEncoding.rawHalfCos
set_option pp.universes false in #print axioms EffectiveEncoding.rawHalfCos
#check EffectiveEncoding.rawHalfSin
set_option pp.universes false in #print axioms EffectiveEncoding.rawHalfSin
#check EffectiveEncoding.AngleCode.rawCos
set_option pp.universes false in #print axioms EffectiveEncoding.AngleCode.rawCos
#check EffectiveEncoding.AngleCode.rawSin
set_option pp.universes false in #print axioms EffectiveEncoding.AngleCode.rawSin
#check EffectiveEncoding.rawPhaseCos
set_option pp.universes false in #print axioms EffectiveEncoding.rawPhaseCos
#check EffectiveEncoding.rawPhaseSin
set_option pp.universes false in #print axioms EffectiveEncoding.rawPhaseSin
#check EffectiveEncoding.SingleCode.rawPacket
set_option pp.universes false in #print axioms EffectiveEncoding.SingleCode.rawPacket
#check EffectiveEncoding.rawProviderHeightBudget
set_option pp.universes false in #print axioms EffectiveEncoding.rawProviderHeightBudget
#check EffectiveEncoding.rawTargetProgramCacheCharge
set_option pp.universes false in #print axioms EffectiveEncoding.rawTargetProgramCacheCharge
#check EffectiveEncoding.rawProviderRootBudget
set_option pp.universes false in #print axioms EffectiveEncoding.rawProviderRootBudget
#check EffectiveEncoding.rawProviderCacheRootCoefficient
set_option pp.universes false in #print axioms EffectiveEncoding.rawProviderCacheRootCoefficient
#check EffectiveEncoding.rawProviderCachePolynomialConstant
set_option pp.universes false in #print axioms EffectiveEncoding.rawProviderCachePolynomialConstant
#check EffectiveEncoding.AngleAtom.rawCosExpression
set_option pp.universes false in #print axioms EffectiveEncoding.AngleAtom.rawCosExpression
#check EffectiveEncoding.AngleAtom.rawSinExpression
set_option pp.universes false in #print axioms EffectiveEncoding.AngleAtom.rawSinExpression
#check EffectiveEncoding.AngleCode.rawCosExpression
set_option pp.universes false in #print axioms EffectiveEncoding.AngleCode.rawCosExpression
#check EffectiveEncoding.AngleCode.rawSinExpression
set_option pp.universes false in #print axioms EffectiveEncoding.AngleCode.rawSinExpression
#check EffectiveEncoding.rawPhaseCosExpression
set_option pp.universes false in #print axioms EffectiveEncoding.rawPhaseCosExpression
#check EffectiveEncoding.rawPhaseSinExpression
set_option pp.universes false in #print axioms EffectiveEncoding.rawPhaseSinExpression
#check EffectiveEncoding.SingleCode.rawPacketExpression
set_option pp.universes false in #print axioms EffectiveEncoding.SingleCode.rawPacketExpression
#check EffectiveEncoding.SingleCode.rawPacketProgram
set_option pp.universes false in #print axioms EffectiveEncoding.SingleCode.rawPacketProgram
#check EffectiveEncoding.sharedRawCachedRun
set_option pp.universes false in #print axioms EffectiveEncoding.sharedRawCachedRun
#check EffectiveEncoding.sharedRawDescriptorRun
set_option pp.universes false in #print axioms EffectiveEncoding.sharedRawDescriptorRun
#check EffectiveEncoding.sharedRawExtractionCode
set_option pp.universes false in #print axioms EffectiveEncoding.sharedRawExtractionCode
#check EffectiveEncoding.gateSharedRawRootCharge
set_option pp.universes false in #print axioms EffectiveEncoding.gateSharedRawRootCharge
#check EffectiveEncoding.extractionSharedRawRootCharge
set_option pp.universes false in #print axioms EffectiveEncoding.extractionSharedRawRootCharge
#check EffectiveEncoding.StoredSwaps
set_option pp.universes false in #print axioms EffectiveEncoding.StoredSwaps
#check EffectiveEncoding.applyStoredSwaps
set_option pp.universes false in #print axioms EffectiveEncoding.applyStoredSwaps
#check EffectiveEncoding.storedSwapPermutation
set_option pp.universes false in #print axioms EffectiveEncoding.storedSwapPermutation
#check EffectiveEncoding.StoredAlignmentRun
set_option pp.universes false in #print axioms EffectiveEncoding.StoredAlignmentRun
#check EffectiveEncoding.storedAlignmentRun
set_option pp.universes false in #print axioms EffectiveEncoding.storedAlignmentRun
#check EffectiveEncoding.storedOccupationStepCode
set_option pp.universes false in #print axioms EffectiveEncoding.storedOccupationStepCode
#check EffectiveEncoding.storedStageCode
set_option pp.universes false in #print axioms EffectiveEncoding.storedStageCode
#check EffectiveEncoding.storedCompressionCode
set_option pp.universes false in #print axioms EffectiveEncoding.storedCompressionCode
#check EffectiveEncoding.storedExtractionCode
set_option pp.universes false in #print axioms EffectiveEncoding.storedExtractionCode
#check EffectiveEncoding.storedSharedRawExtractionCode
set_option pp.universes false in #print axioms EffectiveEncoding.storedSharedRawExtractionCode
#check EffectiveEncoding.stageStoredSwapApplications
set_option pp.universes false in #print axioms EffectiveEncoding.stageStoredSwapApplications
#check EffectiveEncoding.extractionStoredSwapApplications
set_option pp.universes false in #print axioms EffectiveEncoding.extractionStoredSwapApplications
#check CircuitRecursion.binaryDivDigits
set_option pp.universes false in #print axioms CircuitRecursion.binaryDivDigits
#check CircuitRecursion.binaryIntegerDivMod
set_option pp.universes false in #print axioms CircuitRecursion.binaryIntegerDivMod
#check CircuitRecursion.binaryIntegerDiv
set_option pp.universes false in #print axioms CircuitRecursion.binaryIntegerDiv
#check CircuitRecursion.binaryIntegerMod
set_option pp.universes false in #print axioms CircuitRecursion.binaryIntegerMod
#check CircuitRecursion.binaryDivDigitOperations
set_option pp.universes false in #print axioms CircuitRecursion.binaryDivDigitOperations
#check CircuitRecursion.binaryDivOperandTrace
set_option pp.universes false in #print axioms CircuitRecursion.binaryDivOperandTrace
#check CircuitRecursion.binarySqrtDigits
set_option pp.universes false in #print axioms CircuitRecursion.binarySqrtDigits
#check CircuitRecursion.binaryIntegerSqrtFuel
set_option pp.universes false in #print axioms CircuitRecursion.binaryIntegerSqrtFuel
#check CircuitRecursion.binaryIntegerSqrt
set_option pp.universes false in #print axioms CircuitRecursion.binaryIntegerSqrt
#check CircuitRecursion.binarySqrtDigitOperations
set_option pp.universes false in #print axioms CircuitRecursion.binarySqrtDigitOperations
#check CircuitRecursion.binarySqrtOperandTrace
set_option pp.universes false in #print axioms CircuitRecursion.binarySqrtOperandTrace
#check CircuitRecursion.ScalarExpression.binaryProgramOperandTrace
set_option pp.universes false in #print axioms CircuitRecursion.ScalarExpression.binaryProgramOperandTrace
#check CircuitRecursion.PacketExpression.binaryProgramOperandTrace
set_option pp.universes false in #print axioms CircuitRecursion.PacketExpression.binaryProgramOperandTrace
#check CircuitRecursion.ArithmeticWordResult.binaryProgramOperandTrace
set_option pp.universes false in #print axioms CircuitRecursion.ArithmeticWordResult.binaryProgramOperandTrace
#check CircuitRecursion.IntegerScalar.binaryRoot
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalar.binaryRoot
#check CircuitRecursion.ScalarExpression.binaryRootRun
set_option pp.universes false in #print axioms CircuitRecursion.ScalarExpression.binaryRootRun
#check CircuitRecursion.PacketExpression.binaryRootRun
set_option pp.universes false in #print axioms CircuitRecursion.PacketExpression.binaryRootRun
#check CircuitRecursion.IntegerScalar.binaryRootPrimitiveOperations
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalar.binaryRootPrimitiveOperations
#check CircuitRecursion.IntegerScalar.binaryRootOperandTrace
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalar.binaryRootOperandTrace
#check CircuitRecursion.traceTGrowth
set_option pp.universes false in #print axioms CircuitRecursion.traceTGrowth
#check CircuitRecursion.traceSGrowth
set_option pp.universes false in #print axioms CircuitRecursion.traceSGrowth
#check CircuitRecursion.traceRGrowth
set_option pp.universes false in #print axioms CircuitRecursion.traceRGrowth
#check CircuitRecursion.cachedIntegerBudgetConstant
set_option pp.universes false in #print axioms CircuitRecursion.cachedIntegerBudgetConstant
#check CircuitRecursion.ScalarIntegerEvaluation
set_option pp.universes false in #print axioms CircuitRecursion.ScalarIntegerEvaluation
#check CircuitRecursion.PacketIntegerEvaluation
set_option pp.universes false in #print axioms CircuitRecursion.PacketIntegerEvaluation
#check CircuitRecursion.ScalarExpression.costedIntegerRun
set_option pp.universes false in #print axioms CircuitRecursion.ScalarExpression.costedIntegerRun
#check CircuitRecursion.PacketExpression.costedIntegerRun
set_option pp.universes false in #print axioms CircuitRecursion.PacketExpression.costedIntegerRun
#check CircuitRecursion.CostedArithmeticWordResult
set_option pp.universes false in #print axioms CircuitRecursion.CostedArithmeticWordResult
#check CircuitRecursion.costedTracedBase
set_option pp.universes false in #print axioms CircuitRecursion.costedTracedBase
#check CircuitRecursion.costedTracedCorrection
set_option pp.universes false in #print axioms CircuitRecursion.costedTracedCorrection
#check CircuitRecursion.costedTracedPairWord
set_option pp.universes false in #print axioms CircuitRecursion.costedTracedPairWord
#check CircuitRecursion.costedCachedArithmeticRun
set_option pp.universes false in #print axioms CircuitRecursion.costedCachedArithmeticRun
#check CircuitRecursion.ScalarExpression.integerProgramRun
set_option pp.universes false in #print axioms CircuitRecursion.ScalarExpression.integerProgramRun
#check CircuitRecursion.PacketExpression.integerProgramRun
set_option pp.universes false in #print axioms CircuitRecursion.PacketExpression.integerProgramRun
#check CircuitRecursion.integerTracedBase
set_option pp.universes false in #print axioms CircuitRecursion.integerTracedBase
#check CircuitRecursion.integerTracedCorrection
set_option pp.universes false in #print axioms CircuitRecursion.integerTracedCorrection
#check CircuitRecursion.integerTracedPairWord
set_option pp.universes false in #print axioms CircuitRecursion.integerTracedPairWord
#check CircuitRecursion.integerCachedArithmeticRun
set_option pp.universes false in #print axioms CircuitRecursion.integerCachedArithmeticRun
#check CircuitRecursion.IntegerScalar.crossLE
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalar.crossLE
#check CircuitRecursion.integerMinIndex
set_option pp.universes false in #print axioms CircuitRecursion.integerMinIndex
#check CircuitRecursion.integerMaxIndex
set_option pp.universes false in #print axioms CircuitRecursion.integerMaxIndex
#check CircuitRecursion.ScalarExpression.IntegerSubtreeBound
set_option pp.universes false in #print axioms CircuitRecursion.ScalarExpression.IntegerSubtreeBound
#check CircuitRecursion.PacketExpression.IntegerSubtreeBound
set_option pp.universes false in #print axioms CircuitRecursion.PacketExpression.IntegerSubtreeBound
#check CircuitRecursion.ArithmeticWordResult.integerBitBudget
set_option pp.universes false in #print axioms CircuitRecursion.ArithmeticWordResult.integerBitBudget
#check CircuitRecursion.TraceBitBound
set_option pp.universes false in #print axioms CircuitRecursion.TraceBitBound
#check CircuitRecursion.correctionTraceS
set_option pp.universes false in #print axioms CircuitRecursion.correctionTraceS
#check CircuitRecursion.correctionTraceT
set_option pp.universes false in #print axioms CircuitRecursion.correctionTraceT
#check CircuitRecursion.correctionTraceR
set_option pp.universes false in #print axioms CircuitRecursion.correctionTraceR
#check CircuitRecursion.pairTraceT
set_option pp.universes false in #print axioms CircuitRecursion.pairTraceT
#check CircuitRecursion.pairTraceS
set_option pp.universes false in #print axioms CircuitRecursion.pairTraceS
#check CircuitRecursion.pairTraceR
set_option pp.universes false in #print axioms CircuitRecursion.pairTraceR
#check CircuitRecursion.PacketOracleHeight
set_option pp.universes false in #print axioms CircuitRecursion.PacketOracleHeight
#check CircuitRecursion.cachedRationalPacketExpression
set_option pp.universes false in #print axioms CircuitRecursion.cachedRationalPacketExpression
#check CircuitRecursion.rawScalarExpression
set_option pp.universes false in #print axioms CircuitRecursion.rawScalarExpression
#check CircuitRecursion.rawPacketExpression
set_option pp.universes false in #print axioms CircuitRecursion.rawPacketExpression
#check CircuitRecursion.rawPacketExpressionOracle
set_option pp.universes false in #print axioms CircuitRecursion.rawPacketExpressionOracle
#check CircuitRecursion.rawCorrectionOperationOffset
set_option pp.universes false in #print axioms CircuitRecursion.rawCorrectionOperationOffset
#check CircuitRecursion.rawPairOperationOffset
set_option pp.universes false in #print axioms CircuitRecursion.rawPairOperationOffset
#check CircuitRecursion.IntegerScalar.rootOperandTrace
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalar.rootOperandTrace
#check CircuitRecursion.integerStoppingThresholdOperandTrace
set_option pp.universes false in #print axioms CircuitRecursion.integerStoppingThresholdOperandTrace
#check CircuitRecursion.ScalarExpression.binaryRootPrimitiveOperations
set_option pp.universes false in #print axioms CircuitRecursion.ScalarExpression.binaryRootPrimitiveOperations
#check CircuitRecursion.PacketExpression.binaryRootPrimitiveOperations
set_option pp.universes false in #print axioms CircuitRecursion.PacketExpression.binaryRootPrimitiveOperations
#check CircuitRecursion.ArithmeticWordResult.binaryRootPrimitiveOperations
set_option pp.universes false in #print axioms CircuitRecursion.ArithmeticWordResult.binaryRootPrimitiveOperations
#check CircuitRecursion.ScalarExpression.rootOperandTrace
set_option pp.universes false in #print axioms CircuitRecursion.ScalarExpression.rootOperandTrace
#check CircuitRecursion.PacketExpression.rootOperandTrace
set_option pp.universes false in #print axioms CircuitRecursion.PacketExpression.rootOperandTrace
#check CircuitRecursion.ArithmeticWordResult.rootOperandTrace
set_option pp.universes false in #print axioms CircuitRecursion.ArithmeticWordResult.rootOperandTrace
#check CircuitRecursion.IntegerScalar.sharedBinaryRoot
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalar.sharedBinaryRoot
#check CircuitRecursion.ScalarExpression.sharedCostedIntegerRun
set_option pp.universes false in #print axioms CircuitRecursion.ScalarExpression.sharedCostedIntegerRun
#check CircuitRecursion.PacketExpression.sharedCostedIntegerRun
set_option pp.universes false in #print axioms CircuitRecursion.PacketExpression.sharedCostedIntegerRun
#check CircuitRecursion.sharedCostedTracedBase
set_option pp.universes false in #print axioms CircuitRecursion.sharedCostedTracedBase
#check CircuitRecursion.sharedCostedTracedCorrection
set_option pp.universes false in #print axioms CircuitRecursion.sharedCostedTracedCorrection
#check CircuitRecursion.sharedCostedTracedPairWord
set_option pp.universes false in #print axioms CircuitRecursion.sharedCostedTracedPairWord
#check CircuitRecursion.sharedCostedCachedArithmeticRun
set_option pp.universes false in #print axioms CircuitRecursion.sharedCostedCachedArithmeticRun
