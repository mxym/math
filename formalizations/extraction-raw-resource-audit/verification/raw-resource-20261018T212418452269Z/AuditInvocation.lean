import RawResourceAudit
import RawResourceVerification.ReplaySupport

run_cmd (RawResourceVerification.replayAll [
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
  ``CircuitRecursion.sharedCostedCachedArithmeticRun_rootCharge,
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
] "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-kernel")

run_cmd RawResourceVerification.rejectCorruptTheorem ``CircuitRecursion.tracedPairWord_integerBitBudget "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-1"
run_cmd RawResourceVerification.rejectCorruptTheorem ``CircuitRecursion.cachedArithmeticRun_integerBitBudget "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-2"
run_cmd RawResourceVerification.rejectCorruptTheorem ``CircuitRecursion.cachedArithmeticRun_rational_integerBitBudget "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-3"
run_cmd RawResourceVerification.rejectCorruptTheorem ``CircuitRecursion.cachedArithmeticRun_rational_expression_integerSubtreeBound "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-4"
run_cmd RawResourceVerification.rejectCorruptTheorem ``CircuitRecursion.binaryIntegerDivMod_eq "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-5"
run_cmd RawResourceVerification.rejectCorruptTheorem ``CircuitRecursion.binaryIntegerSqrt_eq "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-6"
run_cmd RawResourceVerification.rejectCorruptTheorem ``CircuitRecursion.binaryDivOperandTrace_height "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-7"
run_cmd RawResourceVerification.rejectCorruptTheorem ``CircuitRecursion.binaryIntegerSqrt_operandTrace_height "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-8"
run_cmd RawResourceVerification.rejectCorruptTheorem ``CircuitRecursion.IntegerScalar.binaryRootOperandTrace_bound "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-9"
run_cmd RawResourceVerification.rejectCorruptTheorem ``CircuitRecursion.IntegerScalar.crossLE_value "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-10"
run_cmd RawResourceVerification.rejectCorruptTheorem ``CircuitRecursion.integerMinIndex_eq "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-11"
run_cmd RawResourceVerification.rejectCorruptTheorem ``CircuitRecursion.ScalarExpression.integerProgramRun_eq "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-12"
run_cmd RawResourceVerification.rejectCorruptTheorem ``CircuitRecursion.PacketExpression.integerProgramRun_eq "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-13"
run_cmd RawResourceVerification.rejectCorruptTheorem ``CircuitRecursion.integerCachedArithmeticSU2Synthesis "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-14"
run_cmd RawResourceVerification.rejectCorruptTheorem ``CircuitRecursion.rawScalarExpression_integerProgramRun "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-15"
run_cmd RawResourceVerification.rejectCorruptTheorem ``CircuitRecursion.rawPacketExpression_integerProgramRun "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-16"
run_cmd RawResourceVerification.rejectCorruptTheorem ``CircuitRecursion.rawPacketExpression_operations "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-17"
run_cmd RawResourceVerification.rejectCorruptTheorem ``CircuitRecursion.rawPacketExpression_integerBitBudget "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-18"
run_cmd RawResourceVerification.rejectCorruptTheorem ``CircuitRecursion.ScalarExpression.costedIntegerRun_value "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-19"
run_cmd RawResourceVerification.rejectCorruptTheorem ``CircuitRecursion.PacketExpression.costedIntegerRun_value "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-20"
run_cmd RawResourceVerification.rejectCorruptTheorem ``CircuitRecursion.ScalarExpression.costedIntegerRun_rootCharge "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-21"
run_cmd RawResourceVerification.rejectCorruptTheorem ``CircuitRecursion.PacketExpression.costedIntegerRun_rootCharge "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-22"
run_cmd RawResourceVerification.rejectCorruptTheorem ``CircuitRecursion.costedTracedPairWord_result "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-23"
run_cmd RawResourceVerification.rejectCorruptTheorem ``CircuitRecursion.costedTracedPairWord_rootCharge "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-24"
run_cmd RawResourceVerification.rejectCorruptTheorem ``CircuitRecursion.costedCachedArithmeticRun_rootCharge "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-25"
run_cmd RawResourceVerification.rejectCorruptTheorem ``CircuitRecursion.rawExpressionWord_bound "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-26"
run_cmd RawResourceVerification.rejectCorruptTheorem ``CircuitRecursion.rawTracedCorrection_operations "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-27"
run_cmd RawResourceVerification.rejectCorruptTheorem ``CircuitRecursion.rawTracedPairWord_operations "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-28"
run_cmd RawResourceVerification.rejectCorruptTheorem ``CircuitRecursion.tracedPairWord_twenty_precision_operations "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-29"
run_cmd RawResourceVerification.rejectCorruptTheorem ``CircuitRecursion.costedRawPacketPairWord_operations "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-30"
run_cmd RawResourceVerification.rejectCorruptTheorem ``CircuitRecursion.costedTracedPairWord_twenty_rootCharge "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-31"
run_cmd RawResourceVerification.rejectCorruptTheorem ``CircuitRecursion.ArithmeticWordResult.binaryRootPrimitiveOperations_bound "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-32"
run_cmd RawResourceVerification.rejectCorruptTheorem ``CircuitRecursion.cachedArithmeticRun_binaryRootPrimitiveOperations_polynomial "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-33"
run_cmd RawResourceVerification.rejectCorruptTheorem ``CircuitRecursion.cachedArithmeticRun_binaryProgramOperandTrace_height "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-34"
run_cmd RawResourceVerification.rejectCorruptTheorem ``CircuitRecursion.cachedArithmeticRun_rootOperandTrace_height "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-35"
run_cmd RawResourceVerification.rejectCorruptTheorem ``CircuitRecursion.rawPacketExpressionOracle_bitEnvelope "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-36"
run_cmd RawResourceVerification.rejectCorruptTheorem ``CircuitRecursion.IntegerScalar.crossLE_operands_height "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-37"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.SingleCode.packetExpression_eval "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-38"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.SingleCode.integerPacket_value "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-39"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.extractionCode_provider_resources "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-40"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.providerHeightBudget_polynomial "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-41"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.extractionCode_provider_integerHeight "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-42"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.extractionCode_provider_intermediateHeights "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-43"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.extractionTargetCacheOperations_bound "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-44"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.integerDescriptorSynthesis_eq "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-45"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.integerNumericalExtractionCode_fidelity "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-46"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.actualDescriptorTrace_subtreeBound "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-47"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.extraction_trace_subtree_polynomial "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-48"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.AngleCode.fields_roundtrip "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-49"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.GateCode.fields_roundtrip "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-50"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.extractionCode_fields_roundtrip "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-51"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.extractionCode_fields_length "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-52"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.SingleCode.rawPacket_eq "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-53"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.rawHalfCos_eq "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-54"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.rawPhaseSin_eq "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-55"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.rawCachedIntegerRun_word "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-56"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.rawDescriptorRun_word "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-57"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.rawExtractionCode_eq "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-58"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.rawExtractionCode_length "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-59"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.rawExtractionCode_error "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-60"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.rawExtractionCode_fidelity "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-61"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.rawCachedIntegerRun_integerBitBudget "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-62"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.rawDescriptorRun_polynomial "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-63"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.rawExtraction_expression_subtreeBound "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-64"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.rawExtraction_integerProgramRun_height "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-65"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.costedRawCachedRun_result "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-66"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.costedRawCachedRun_rootCharge "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-67"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.costedRawExtractionCode_eq "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-68"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.costedRawExtractionCode_fidelity "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-69"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.costedRawDescriptorRun_binaryProgramOperandTrace_height "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-70"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.extractionPrecision_logarithmic "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-71"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.rawExtraction_integerBitBudget_logarithmic "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-72"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.rawTargetCache_height_logarithmic "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-73"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.countedProgramFields_erase "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-74"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.extractionCode_countedFields_roundtrip "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-75"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.extractionCode_countedFields_steps "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-76"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.extractionCode_countedFields_steps_polynomial "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-77"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.costedRawCachedRun_operations "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-78"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.costedRawDescriptorRun_rootCharge_polynomial "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-79"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.costedRawDescriptorRun_rootCharge_logarithmic "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-80"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.extractionRawRootCharge_bound "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-81"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.extractionRawRootCharge_polynomial "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-82"
run_cmd RawResourceVerification.rejectCorruptTheorem ``CircuitRecursion.IntegerScalar.sharedBinaryRoot_value "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-83"
run_cmd RawResourceVerification.rejectCorruptTheorem ``CircuitRecursion.IntegerScalar.sharedBinaryRoot_charge "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-84"
run_cmd RawResourceVerification.rejectCorruptTheorem ``CircuitRecursion.IntegerScalar.sharedBinaryRoot_eq "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-85"
run_cmd RawResourceVerification.rejectCorruptTheorem ``CircuitRecursion.IntegerScalar.sharedBinaryRoot_height "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-86"
run_cmd RawResourceVerification.rejectCorruptTheorem ``CircuitRecursion.IntegerScalar.sharedBinaryRoot_charge_bound "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-87"
run_cmd RawResourceVerification.rejectCorruptTheorem ``CircuitRecursion.ScalarExpression.sharedCostedIntegerRun_value "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-88"
run_cmd RawResourceVerification.rejectCorruptTheorem ``CircuitRecursion.PacketExpression.sharedCostedIntegerRun_value "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-89"
run_cmd RawResourceVerification.rejectCorruptTheorem ``CircuitRecursion.ScalarExpression.sharedCostedIntegerRun_rootCharge "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-90"
run_cmd RawResourceVerification.rejectCorruptTheorem ``CircuitRecursion.PacketExpression.sharedCostedIntegerRun_rootCharge "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-91"
run_cmd RawResourceVerification.rejectCorruptTheorem ``CircuitRecursion.ScalarExpression.sharedCostedIntegerRun_eq "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-92"
run_cmd RawResourceVerification.rejectCorruptTheorem ``CircuitRecursion.PacketExpression.sharedCostedIntegerRun_eq "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-93"
run_cmd RawResourceVerification.rejectCorruptTheorem ``CircuitRecursion.sharedCostedTracedPairWord_eq "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-94"
run_cmd RawResourceVerification.rejectCorruptTheorem ``CircuitRecursion.sharedCostedTracedPairWord_rootCharge "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-95"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.sharedRawCachedRun_eq "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-96"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.sharedRawExtractionCode_eq "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-97"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.sharedRawExtractionCode_error "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-98"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.sharedRawExtractionCode_fidelity "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-99"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.extractionSharedRawRootCharge_bound "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-100"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.rawTargetProgramCache_values "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-101"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.targetProgramDescriptorRun_result "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-102"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.targetProgramDescriptorRun_rootCharge "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-103"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.targetProgramDescriptorRun_rootCharge_bound "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-104"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.chargedProviderExtractionCode_eq "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-105"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.chargedProviderExtractionCode_fidelity "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-106"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.extractionProviderProgramRootCharge_bound "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-107"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.AngleCode.rawExpression_operations "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-108"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.SingleCode.rawPacketExpression_operations "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-109"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.SingleCode.rawPacketExpression_budget "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-110"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.extractionCode_rawProviderExpression_budget "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-111"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.extractionCode_rawPacketProgram_rootCharge "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-112"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.extractionCode_rawProviderExpression_subtreeBound "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-113"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.extractionCode_rawProviderExpression_binaryProgramOperandTrace_height "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-114"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.rawTargetProgramCacheCharge_bound "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-115"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.rawTargetProgramCacheCharge_polynomial "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-116"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.rawProviderCacheRootCoefficient_polynomial "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-117"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.rawTargetProgramCacheCharge_polynomial_kq "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-118"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.AngleAtom.rawCosExpression_run "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-119"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.AngleAtom.rawSinExpression_run "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-120"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.AngleCode.rawCosExpression_run "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-121"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.AngleCode.rawSinExpression_run "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-122"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.rawPhaseCosExpression_run "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-123"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.rawPhaseSinExpression_run "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-124"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.SingleCode.rawPacketExpression_run "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-125"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.SingleCode.rawPacketProgram_value "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-126"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.applyStoredSwaps_value "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-127"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.applyStoredSwaps_count "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-128"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.storedAlignmentRun_word "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-129"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.storedAlignmentRun_count "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-130"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.storedExtractionCode_eq "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-131"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.storedSharedRawExtractionCode_eq "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-132"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.storedSharedRawExtractionCode_fidelity "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-133"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.stageStoredSwapApplications_exact "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-134"
run_cmd RawResourceVerification.rejectCorruptTheorem ``EffectiveEncoding.extractionStoredSwapApplications_bound "/mnt/lean-research-d/worktrees/extraction-independent-review-20261019/formalizations/extraction-raw-resource-audit/verification/raw-resource-20261018T212418452269Z/raw-resource-control-135"
