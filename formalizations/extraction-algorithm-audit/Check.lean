import AlgorithmAudit
import AlgorithmVerification.ReplaySupport

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true

run_cmd (AlgorithmVerification.checkKinds [
  ``CircuitRecursion.expressionAdd_eval,
  ``CircuitRecursion.expressionNeg_eval,
  ``CircuitRecursion.expressionMul_eval,
  ``CircuitRecursion.expressionInv_eval,
  ``CircuitRecursion.expressionSqrt_eval,
  ``CircuitRecursion.expressionMeanMinus_eval,
  ``CircuitRecursion.expressionCoordinate_eval,
  ``CircuitRecursion.expressionPacketMul_eval,
  ``CircuitRecursion.expressionPacketInverse_eval,
  ``CircuitRecursion.expressionPacketOne_eval,
  ``CircuitRecursion.expressionFrame_eval,
  ``CircuitRecursion.expressionDistance_eval,
  ``CircuitRecursion.balancedParameterFacts,
  ``CircuitRecursion.balancedCircle,
  ``CircuitRecursion.balancedReference_scalar,
  ``CircuitRecursion.referenceX_distance,
  ``CircuitRecursion.referenceY_distance,
  ``CircuitRecursion.coordinateOracle_correct,
  ``CircuitRecursion.balancedSOracle_correct,
  ``CircuitRecursion.balancedCOracle_correct,
  ``CircuitRecursion.referenceXOracle_correct,
  ``CircuitRecursion.referenceYOracle_correct,
  ``CircuitRecursion.balancedReferenceOracle_correct,
  ``CircuitRecursion.cachedNumericalRun_query_bounds,
  ``CircuitRecursion.cachedNumericalRun_precision_bounds,
  ``CircuitRecursion.dyadic_numerator_bits,
  ``CircuitRecursion.dyadicPacketBits_bound,
  ``CircuitRecursion.cachedInputBits_bound,
  ``CircuitRecursion.cachedInputBits_precision_bound,
  ``CircuitRecursion.cachedArithmeticRun_word,
  ``CircuitRecursion.cachedArithmeticRun_operations,
  ``CircuitRecursion.cachedArithmeticRun_executedOperations,
  ``CircuitRecursion.cachedArithmeticSU2Synthesis,
  ``CircuitRecursion.buildPacketCache_agrees,
  ``CircuitRecursion.buildPacketCache_requests,
  ``CircuitRecursion.buildPacketCache_precision,
  ``CircuitRecursion.cachedNumericalRun_word,
  ``CircuitRecursion.cachedNumericalRun_gateRequests,
  ``CircuitRecursion.cachedNumericalRun_targetRequests,
  ``CircuitRecursion.cachedNumericalRun_gatePrecision,
  ``CircuitRecursion.cachedNumericalRun_targetPrecision,
  ``CircuitRecursion.cachedNumericalSU2Synthesis,
  ``CircuitRecursion.quaternionConjugateOracle_correct,
  ``CircuitRecursion.conditionedFactors_correct,
  ``CircuitRecursion.quaternionCoordinates_inverse,
  ``CircuitRecursion.quaternionOracleInverse_correct,
  ``CircuitRecursion.frameOracle_correct,
  ``CircuitRecursion.chartTargetOracle_correct,
  ``CircuitRecursion.intertwinerMass_distance,
  ``CircuitRecursion.chartMassScore_correct,
  ``CircuitRecursion.dyadic_square_precision,
  ``CircuitRecursion.chooseChart_denominator,
  ``CircuitRecursion.residualSmall_correct,
  ``CircuitRecursion.ScalarExpression.executedOperations_le,
  ``CircuitRecursion.PacketExpression.executedOperations_le,
  ``CircuitRecursion.ArithmeticWordResult.executedOperations_le,
  ``CircuitRecursion.expressionPowerTwo_eq,
  ``CircuitRecursion.executeExpressionRoot_correct,
  ``CircuitRecursion.executeStoppingThreshold_correct,
  ``CircuitRecursion.ScalarExpression.run_correct,
  ``CircuitRecursion.PacketExpression.run_correct,
  ``CircuitRecursion.expressionAdd_bound,
  ``CircuitRecursion.expressionNeg_bound,
  ``CircuitRecursion.expressionMul_bound,
  ``CircuitRecursion.expressionInv_bound,
  ``CircuitRecursion.expressionSqrt_bound,
  ``CircuitRecursion.expressionMeanMinus_bound,
  ``CircuitRecursion.expressionCoordinate_bound,
  ``CircuitRecursion.expressionPacketMul_bound,
  ``CircuitRecursion.expressionPacketInverse_bound,
  ``CircuitRecursion.expressionDistance_bound,
  ``CircuitRecursion.expressionBalancedS_bound,
  ``CircuitRecursion.expressionBalancedC_bound,
  ``CircuitRecursion.expressionReferenceX_bound,
  ``CircuitRecursion.expressionReferenceY_bound,
  ``CircuitRecursion.expressionBalancedReference_bound,
  ``CircuitRecursion.expressionChartTarget_bound,
  ``CircuitRecursion.expressionChartMass_bound,
  ``CircuitRecursion.expressionNormalized_bound,
  ``CircuitRecursion.expressionConjugator_bound,
  ``CircuitRecursion.expressionFactor_bounds,
  ``CircuitRecursion.bitAdd_bound,
  ``CircuitRecursion.bitNeg_bound,
  ``CircuitRecursion.bitMul_bound,
  ``CircuitRecursion.bitInv_bound,
  ``CircuitRecursion.bitSqrt_bound,
  ``CircuitRecursion.bitMean_bound,
  ``CircuitRecursion.bitCoordinate_bound,
  ``CircuitRecursion.bitPacketMul_bound,
  ``CircuitRecursion.bitPacketInverse_bound,
  ``CircuitRecursion.bitDistance_bound,
  ``CircuitRecursion.rationalBinaryExponent_zero,
  ``CircuitRecursion.rationalBinaryExponent_one,
  ``CircuitRecursion.bitFrame_bound,
  ``CircuitRecursion.bitBalancedS_bound,
  ``CircuitRecursion.bitBalancedC_bound,
  ``CircuitRecursion.bitReference_bounds,
  ``CircuitRecursion.bitBalancedReference_bound,
  ``CircuitRecursion.bitChartTarget_bound,
  ``CircuitRecursion.bitChartMass_bound,
  ``CircuitRecursion.bitNormalized_bound,
  ``CircuitRecursion.bitConjugator_bound,
  ``CircuitRecursion.bitFactor_bounds,
  ``CircuitRecursion.fixedFactor_integerBitBudget,
  ``CircuitRecursion.chooseChart_agrees,
  ``CircuitRecursion.coordinateSubOracle_agrees,
  ``CircuitRecursion.intertwinerRadiusOracle_agrees,
  ``CircuitRecursion.normalizedIntertwinerOracle_agrees,
  ``CircuitRecursion.conditionedConjugatorOracle_agrees,
  ``CircuitRecursion.conditionedFactorXOracle_agrees,
  ``CircuitRecursion.conditionedFactorYOracle_agrees,
  ``CircuitRecursion.expressionBalancedS_eval,
  ``CircuitRecursion.expressionBalancedC_eval,
  ``CircuitRecursion.expressionReferenceX_eval,
  ``CircuitRecursion.expressionReferenceY_eval,
  ``CircuitRecursion.expressionBalancedReference_eval,
  ``CircuitRecursion.expressionChartTarget_eval,
  ``CircuitRecursion.expressionChartMass_eval,
  ``CircuitRecursion.expressionRadius_eval,
  ``CircuitRecursion.expressionNormalized_eval,
  ``CircuitRecursion.expressionConjugator_eval,
  ``CircuitRecursion.expressionConjugate_eval,
  ``CircuitRecursion.expressionFactorX_eval,
  ``CircuitRecursion.expressionFactorY_eval,
  ``CircuitRecursion.cachedPacketExpression_bitEnvelope,
  ``CircuitRecursion.expressionPacketOne_bitEnvelope,
  ``CircuitRecursion.expressionWord_bitEnvelope,
  ``CircuitRecursion.residual_bitEnvelope,
  ``CircuitRecursion.cachedResidualFactor_integerHeight,
  ``CircuitRecursion.rationalBinaryExponent_height,
  ``CircuitRecursion.rationalBinaryExponent_le,
  ``CircuitRecursion.ScalarExpression.integerRun_height,
  ``CircuitRecursion.PacketExpression.integerRun_height,
  ``CircuitRecursion.IntegerScalar.meanMinus_value,
  ``CircuitRecursion.IntegerScalarHeight.mono,
  ``CircuitRecursion.IntegerScalar.meanMinus_height,
  ``CircuitRecursion.integerStoppingThreshold_value,
  ``CircuitRecursion.rationalSqrtApprox_max,
  ``CircuitRecursion.ScalarExpression.integerRun_correct,
  ``CircuitRecursion.PacketExpression.integerRun_correct,
  ``CircuitRecursion.IntegerPacket.inverse_value,
  ``CircuitRecursion.IntegerPacket.inverse_height,
  ``CircuitRecursion.IntegerPacket.distanceScalar_value,
  ``CircuitRecursion.IntegerPacket.distanceNumerator_bound,
  ``CircuitRecursion.IntegerPacket.distanceScalar_height,
  ``CircuitRecursion.IntegerPacket.mul_value,
  ``CircuitRecursion.quaternionSign_natAbs,
  ``CircuitRecursion.integerQuaternionProduct_bound,
  ``CircuitRecursion.IntegerPacketHeight.mono,
  ``CircuitRecursion.IntegerPacket.one_height,
  ``CircuitRecursion.IntegerPacket.mul_height,
  ``CircuitRecursion.integerPacketWord_value,
  ``CircuitRecursion.integerPacketWord_height,
  ``CircuitRecursion.dyadicIntegerPacket_value,
  ``CircuitRecursion.dyadicIntegerPacket_height,
  ``CircuitRecursion.IntegerPacket.one_value,
  ``CircuitRecursion.cachedIntegerPacket_value,
  ``CircuitRecursion.cachedIntegerPacket_height,
  ``CircuitRecursion.cachedIntegerPacketWord_height,
  ``CircuitRecursion.cachedIntegerPacketWord_value,
  ``CircuitRecursion.commonDenominator_binary_bound,
  ``CircuitRecursion.IntegerPacketHeight.binary_bounds,
  ``CircuitRecursion.cachedSynthesisWord_integerHeight,
  ``CircuitRecursion.IntegerScalar.add_value,
  ``CircuitRecursion.IntegerScalar.neg_value,
  ``CircuitRecursion.IntegerScalar.mul_value,
  ``CircuitRecursion.IntegerScalar.inv_value,
  ``CircuitRecursion.IntegerScalar.add_height,
  ``CircuitRecursion.IntegerScalar.neg_height,
  ``CircuitRecursion.IntegerScalar.mul_height,
  ``CircuitRecursion.IntegerScalar.inv_height,
  ``CircuitRecursion.IntegerScalar.max_value,
  ``CircuitRecursion.IntegerScalar.root_value,
  ``CircuitRecursion.IntegerScalar.root_height,
  ``CircuitRecursion.IntegerScalar.ofRat_value,
  ``CircuitRecursion.IntegerScalar.canonical_height,
  ``CircuitRecursion.IntegerPacket.coordinate_value,
  ``CircuitRecursion.IntegerPacket.coordinate_height,
  ``CircuitRecursion.IntegerPacket.ofScalars_value,
  ``CircuitRecursion.product_denominator_bound,
  ``CircuitRecursion.IntegerPacket.ofScalars_height,
  ``CircuitRecursion.IntegerPacket.ofVector_value,
  ``CircuitRecursion.IntegerPacket.ofVector_height,
  ``CircuitRecursion.normalizedQuaternionSU2_unitary,
  ``CircuitRecursion.normalizedIntertwiner_coordinates,
  ``CircuitRecursion.coordinateSubOracle_correct,
  ``CircuitRecursion.normalizedIntertwinerOracle_correct,
  ``CircuitRecursion.numericalCorrection_length,
  ``CircuitRecursion.numericalCorrection_error,
  ``CircuitRecursion.quaternionWordOracle_agrees,
  ``CircuitRecursion.fixedNetWord_agrees,
  ``CircuitRecursion.residualSmall_agrees,
  ``CircuitRecursion.correctionDemand_ge,
  ``CircuitRecursion.numericalCorrection_agrees,
  ``CircuitRecursion.numericalDemand_ge,
  ``CircuitRecursion.numericalPairWord_agrees,
  ``CircuitRecursion.numericalDemand_succ,
  ``CircuitRecursion.numericalDemand_bound,
  ``CircuitRecursion.numericalDemand_precision_bound,
  ``CircuitRecursion.expressionWord_bound,
  ``CircuitRecursion.tracedBase_operations,
  ``CircuitRecursion.tracedCorrection_operations,
  ``CircuitRecursion.tracedPairWord_operations,
  ``CircuitRecursion.numerical_stop_budget,
  ``CircuitRecursion.numericalDoubleCorrection_error,
  ``CircuitRecursion.numericalThreshold_error,
  ``CircuitRecursion.numericalThreshold_depth_bound,
  ``CircuitRecursion.numericalPairWord_error,
  ``CircuitRecursion.numericalPairWord_length,
  ``CircuitRecursion.numericalSU2Synthesis,
  ``CircuitRecursion.numericalSU2Synthesis_dyadic,
  ``CircuitRecursion.pairOperationSlope_pos,
  ``CircuitRecursion.pairOperationSlope_bound,
  ``CircuitRecursion.pairOperationSlope_length_bound,
  ``CircuitRecursion.pairedOffset_step_bound,
  ``CircuitRecursion.pairOperationOffset_bound,
  ``CircuitRecursion.tracedPairWord_literal_operations,
  ``CircuitRecursion.offsetGrowth_precision_bound,
  ``CircuitRecursion.AgreesThrough.mono,
  ``CircuitRecursion.AgreesThrough.refl,
  ``CircuitRecursion.oracleAdd_agrees,
  ``CircuitRecursion.oracleNeg_agrees,
  ``CircuitRecursion.oracleMul_agrees,
  ``CircuitRecursion.oracleInv_agrees,
  ``CircuitRecursion.oracleSqrt_agrees,
  ``CircuitRecursion.oracleMeanMinus_agrees,
  ``CircuitRecursion.coordinateOracle_agrees,
  ``CircuitRecursion.quaternionOracleMul_agrees,
  ``CircuitRecursion.quaternionOracleInverse_agrees,
  ``CircuitRecursion.quaternionConjugateOracle_agrees,
  ``CircuitRecursion.balancedSOracle_agrees,
  ``CircuitRecursion.balancedCOracle_agrees,
  ``CircuitRecursion.referenceXOracle_agrees,
  ``CircuitRecursion.referenceYOracle_agrees,
  ``CircuitRecursion.balancedReferenceOracle_agrees,
  ``CircuitRecursion.chartTargetOracle_agrees,
  ``CircuitRecursion.distanceScore_agrees,
  ``CircuitRecursion.chartMassScore_agrees,
  ``CircuitRecursion.expressionWord_eval,
  ``CircuitRecursion.tracedBase_word,
  ``CircuitRecursion.tracedCorrection_word,
  ``CircuitRecursion.tracedPairWord_word,
  ``EffectiveEncoding.mergeAngle_degenerate,
  ``EffectiveEncoding.AngleAtom.cosOracle_correct,
  ``EffectiveEncoding.AngleAtom.sinOracle_correct,
  ``EffectiveEncoding.AngleAtom.value_bounds,
  ``EffectiveEncoding.AngleCode.cosOracle_correct,
  ``EffectiveEncoding.AngleCode.sinOracle_correct,
  ``EffectiveEncoding.AngleCode.evaluation,
  ``EffectiveEncoding.interpret_flatMap,
  ``EffectiveEncoding.allBranchCode_action,
  ``EffectiveEncoding.allBranchCode_length,
  ``EffectiveEncoding.occupationStepCode_action,
  ``EffectiveEncoding.occupationStepCode_length,
  ``EffectiveEncoding.prefixCode_length,
  ``EffectiveEncoding.interpret_prefix,
  ``EffectiveEncoding.shiftCode_length,
  ``EffectiveEncoding.interpret_shift,
  ``EffectiveEncoding.stageCircuit_action,
  ``EffectiveEncoding.compressionCircuit_succ,
  ``EffectiveEncoding.bitOccupation_zero,
  ``EffectiveEncoding.compressionCircuit_action,
  ``EffectiveEncoding.stageCode_length,
  ``EffectiveEncoding.compressionCode_length,
  ``EffectiveEncoding.compressionCircuit_matrix,
  ``EffectiveEncoding.compressionCircuit_coherent,
  ``EffectiveEncoding.compressionCircuit_purePower,
  ``EffectiveEncoding.AngleCode.Fits.mono,
  ``EffectiveEncoding.AngleCode.Fits.neg,
  ``EffectiveEncoding.AngleCode.Fits.half,
  ``EffectiveEncoding.SingleCode.Fits.mono,
  ``EffectiveEncoding.GateCode.Fits.mono,
  ``EffectiveEncoding.WordFits.mono,
  ``EffectiveEncoding.wordFits_nil,
  ``EffectiveEncoding.wordFits_append,
  ``EffectiveEncoding.WordFits.reverse,
  ``EffectiveEncoding.cnotCode_fits,
  ``EffectiveEncoding.parityCode_fits,
  ``EffectiveEncoding.pauliCode_fits,
  ``EffectiveEncoding.signedCode_fits,
  ``EffectiveEncoding.selectedCode_fits,
  ``EffectiveEncoding.piCode_fits,
  ``EffectiveEncoding.hadamardCode_fits,
  ``EffectiveEncoding.adjacentSwapCode_fits,
  ``EffectiveEncoding.adjacentRotationCode_fits,
  ``EffectiveEncoding.orientedRotationCode_fits,
  ``EffectiveEncoding.moveCode_fits,
  ``EffectiveEncoding.swapCode_fits,
  ``EffectiveEncoding.rotationCode_fits,
  ``EffectiveEncoding.RawCode.compile_fits,
  ``EffectiveEncoding.compileRaw_fits,
  ``EffectiveEncoding.alignmentCode_fits,
  ``EffectiveEncoding.countProgram_fits,
  ``EffectiveEncoding.branchCode_fits,
  ``EffectiveEncoding.occupationStepCode_fits,
  ``EffectiveEncoding.halvingBudget_mono,
  ``EffectiveEncoding.stageCode_fits,
  ``EffectiveEncoding.WordFits.shift,
  ``EffectiveEncoding.WordFits.prefix,
  ``EffectiveEncoding.WordFits.cast,
  ``EffectiveEncoding.compressionCode_fits,
  ``EffectiveEncoding.bellPairsCode_fits,
  ``EffectiveEncoding.extractionCode_fits,
  ``EffectiveEncoding.binaryWidth_mono,
  ``EffectiveEncoding.AngleCode.descriptionWeight_bound,
  ``EffectiveEncoding.SingleCode.descriptionWeight_bound,
  ``EffectiveEncoding.GateCode.descriptionWeight_bound,
  ``EffectiveEncoding.codeDescriptionWeight_bound,
  ``EffectiveEncoding.extractionCode_descriptionWeight,
  ``EffectiveEncoding.AngleCode.neg_value,
  ``EffectiveEncoding.AngleCode.half_value,
  ``EffectiveEncoding.piCode_value,
  ``EffectiveEncoding.GateCode.inverse_value,
  ``EffectiveEncoding.interpret_length,
  ``EffectiveEncoding.interpret_append,
  ``EffectiveEncoding.interpret_reverse,
  ``EffectiveEncoding.reverseCode_length,
  ``EffectiveEncoding.maskOfBits_injective,
  ``EffectiveEncoding.maskIndex_injective,
  ``EffectiveEncoding.masks_nodup,
  ``EffectiveEncoding.mem_masks,
  ``EffectiveEncoding.masks_length,
  ``EffectiveEncoding.masks_perm,
  ``EffectiveEncoding.controls_length,
  ``EffectiveEncoding.controls_character,
  ``EffectiveEncoding.interpret_cnotCode,
  ``EffectiveEncoding.parityCode_action,
  ``EffectiveEncoding.parityCode_length,
  ``EffectiveEncoding.pauliCode_action,
  ``EffectiveEncoding.pauliCode_length,
  ``EffectiveEncoding.signedCode_value,
  ``EffectiveEncoding.maskParity_sign,
  ``EffectiveEncoding.run_pauliCodes,
  ``EffectiveEncoding.selectedCode_action,
  ``EffectiveEncoding.selectedCode_length,
  ``EffectiveEncoding.mem_triples,
  ``EffectiveEncoding.triples_nodup,
  ``EffectiveEncoding.fromTriple_count_zero,
  ``EffectiveEncoding.fromTriple_count_one,
  ``EffectiveEncoding.fromTriple_count_two,
  ``EffectiveEncoding.fromTriple_count_three,
  ``EffectiveEncoding.count_total,
  ``EffectiveEncoding.toTriple_le,
  ``EffectiveEncoding.toTriple_fromTriple,
  ``EffectiveEncoding.fromTriple_toTriple,
  ``EffectiveEncoding.occupations_nodup,
  ``EffectiveEncoding.mem_occupations,
  ``EffectiveEncoding.occupations_length,
  ``EffectiveEncoding.unrank_rank,
  ``EffectiveEncoding.rank_unrank,
  ``EffectiveEncoding.boundedBits_injective,
  ``EffectiveEncoding.rank_fits,
  ``EffectiveEncoding.find_unique,
  ``EffectiveEncoding.decode_encode,
  ``EffectiveEncoding.decode_some_iff,
  ``EffectiveEncoding.enumeration_candidate_bound,
  ``EffectiveEncoding.compactEncoding_testBit,
  ``EffectiveEncoding.originalEncoding_high_zero,
  ``EffectiveEncoding.interpret_cast,
  ``EffectiveEncoding.castCode_length,
  ``EffectiveEncoding.interpret_bellPreparationCode,
  ``EffectiveEncoding.interpret_bellPairsCode,
  ``EffectiveEncoding.extractionCircuit_eq,
  ``EffectiveEncoding.extractionCircuit_gate,
  ``EffectiveEncoding.extractionCircuit_coherent,
  ``EffectiveEncoding.extractionCircuit_purePower,
  ``EffectiveEncoding.extractionCode_length,
  ``EffectiveEncoding.extractionCode_polynomial_bound,
  ``EffectiveEncoding.extractionCircuit_polynomial_bound,
  ``EffectiveEncoding.extractionVector_readout,
  ``EffectiveEncoding.garbageVector_square,
  ``EffectiveEncoding.extractionOutput_coherent,
  ``EffectiveEncoding.extractionOutput_purePower,
  ``EffectiveEncoding.wireLabels_value,
  ``EffectiveEncoding.labelCircuit_flatMap,
  ``EffectiveEncoding.labelCircuit_uses,
  ``EffectiveEncoding.compileLabels_error,
  ``EffectiveEncoding.compileLabelWord_error,
  ``EffectiveEncoding.compileLabels_length,
  ``EffectiveEncoding.compileLabelWord_length,
  ``EffectiveEncoding.extractionOutput_fidelity_one,
  ``EffectiveEncoding.extractionOutput_robust,
  ``EffectiveEncoding.extractionOutput_robust_up_to_phase,
  ``EffectiveEncoding.finiteLabels_fidelity,
  ``EffectiveEncoding.selectedCode_run_eq,
  ``EffectiveEncoding.adjacentSwapCode_run_eq,
  ``EffectiveEncoding.adjacentSwapCode_length,
  ``EffectiveEncoding.adjacentRotationCode_run_eq,
  ``EffectiveEncoding.adjacentRotationCode_length,
  ``EffectiveEncoding.orientedRotationCode_run_eq,
  ``EffectiveEncoding.mem_otherWires,
  ``EffectiveEncoding.otherWires_length,
  ``EffectiveEncoding.differing_exists,
  ``EffectiveEncoding.differingWire_spec,
  ``EffectiveEncoding.clearBits_otherWires,
  ``EffectiveEncoding.moveCode_run_eq,
  ``EffectiveEncoding.moveCode_length,
  ``EffectiveEncoding.swapCode_action,
  ``EffectiveEncoding.swapCode_length,
  ``EffectiveEncoding.rotationCode_action,
  ``EffectiveEncoding.rotationCode_length,
  ``EffectiveEncoding.GateCode.globalPhase_norm,
  ``EffectiveEncoding.GateCode.representative_spec,
  ``EffectiveEncoding.wordPhase_norm,
  ``EffectiveEncoding.interpret_cons,
  ``EffectiveEncoding.representativeCircuit_cons,
  ``EffectiveEncoding.representativeCircuit_phase,
  ``EffectiveEncoding.descriptor_word_error,
  ``EffectiveEncoding.descriptor_word_uniform_error,
  ``EffectiveEncoding.descriptorSynthesis_spec,
  ``EffectiveEncoding.numericalExtractionCode_uses,
  ``EffectiveEncoding.numericalExtractionCode_error,
  ``EffectiveEncoding.numericalExtractionCode_length,
  ``EffectiveEncoding.numericalExtractionCode_fidelity,
  ``EffectiveEncoding.descriptorArithmeticOperations_bound,
  ``EffectiveEncoding.extractionArithmeticOperations_bound,
  ``EffectiveEncoding.numericalExtraction_from_universal,
  ``EffectiveEncoding.countProgram_length,
  ``EffectiveEncoding.countProgram_sparse,
  ``EffectiveEncoding.indexedCount_image,
  ``EffectiveEncoding.indexedCount_ratio,
  ``EffectiveEncoding.explicitOthers_perm,
  ``EffectiveEncoding.explicitOthers_nodup,
  ``EffectiveEncoding.explicitOthers_length,
  ``EffectiveEncoding.integerIndexedCode_raw,
  ``EffectiveEncoding.integerIndexedCode_action,
  ``EffectiveEncoding.integerIndexedCode_fixes_zero,
  ``EffectiveEncoding.integerIndexedCode_length,
  ``EffectiveEncoding.branchEmbedding_eq,
  ``EffectiveEncoding.branchCode_action,
  ``EffectiveEncoding.branchCode_fixes_other,
  ``EffectiveEncoding.branchCode_fixes_other_pivot,
  ``EffectiveEncoding.branchCode_length,
  ``EffectiveEncoding.swapCode_denote,
  ``EffectiveEncoding.rotationCode_denote_eq,
  ``EffectiveEncoding.mergeCode_value,
  ``EffectiveEncoding.RawCode.compile_denote,
  ``EffectiveEncoding.RawCode.compile_length,
  ``EffectiveEncoding.compileRaw_denote,
  ``EffectiveEncoding.compileRaw_length,
  ``EffectiveEncoding.alignmentPerm_complete,
  ``EffectiveEncoding.alignmentCode_action,
  ``EffectiveEncoding.alignmentCode_length,
  ``EffectiveEncoding.alignmentCode_on_embedding,
  ``EffectiveEncoding.star_complexPhase,
  ``EffectiveEncoding.phaseRepresentative_bool,
  ``EffectiveEncoding.su2ToBool_star,
  ``EffectiveEncoding.SingleCode.globalPhase_norm,
  ``EffectiveEncoding.SingleCode.representative_spec,
  ``EffectiveEncoding.quaternionCoordinates_star,
  ``EffectiveEncoding.sqrt_half_eq_invSqrtTwo,
  ``EffectiveEncoding.invSqrtTwoOracle_correct,
  ``EffectiveEncoding.phaseCosOracle_correct,
  ``EffectiveEncoding.phaseSinOracle_correct,
  ``EffectiveEncoding.quaternionStarOracle_correct,
  ``EffectiveEncoding.coordinatePacket_correct,
  ``EffectiveEncoding.hadRepresentative_coordinates,
  ``EffectiveEncoding.phaseRepresentative_coordinates,
  ``EffectiveEncoding.SingleCode.quaternionOracle_correct
] [
  ``CircuitRecursion.ScalarExpression,
  ``CircuitRecursion.PacketExpression,
  ``CircuitRecursion.ScalarExpression.eval,
  ``CircuitRecursion.PacketExpression.eval,
  ``CircuitRecursion.ScalarExpression.operations,
  ``CircuitRecursion.PacketExpression.operations,
  ``CircuitRecursion.ScalarExpressionOracle,
  ``CircuitRecursion.PacketExpressionOracle,
  ``CircuitRecursion.evaluateScalarOracle,
  ``CircuitRecursion.evaluatePacketOracle,
  ``CircuitRecursion.expressionAdd,
  ``CircuitRecursion.expressionNeg,
  ``CircuitRecursion.expressionMul,
  ``CircuitRecursion.expressionInv,
  ``CircuitRecursion.expressionSqrt,
  ``CircuitRecursion.expressionMeanMinus,
  ``CircuitRecursion.expressionCoordinate,
  ``CircuitRecursion.expressionPacketMul,
  ``CircuitRecursion.expressionPacketInverse,
  ``CircuitRecursion.expressionPacketOne,
  ``CircuitRecursion.expressionFrame,
  ``CircuitRecursion.expressionDistance,
  ``CircuitRecursion.balancedS,
  ``CircuitRecursion.balancedC,
  ``CircuitRecursion.referenceX,
  ``CircuitRecursion.referenceY,
  ``CircuitRecursion.balancedReference,
  ``CircuitRecursion.coordinateOracle,
  ``CircuitRecursion.balancedSOracle,
  ``CircuitRecursion.balancedCOracle,
  ``CircuitRecursion.referenceXOracle,
  ``CircuitRecursion.referenceYOracle,
  ``CircuitRecursion.balancedReferenceOracle,
  ``CircuitRecursion.cachePrecisionBudget,
  ``CircuitRecursion.dyadicPacketBits,
  ``CircuitRecursion.cachedInputBits,
  ``CircuitRecursion.cachedArithmeticRun,
  ``CircuitRecursion.buildPacketCache,
  ``CircuitRecursion.readPacketCache,
  ``CircuitRecursion.CachedWordResult,
  ``CircuitRecursion.cachedNumericalRun,
  ``CircuitRecursion.quaternionConjugateOracle,
  ``CircuitRecursion.conditionedConjugatorOracle,
  ``CircuitRecursion.conditionedFactorXOracle,
  ``CircuitRecursion.conditionedFactorYOracle,
  ``CircuitRecursion.quaternionOracleInverse,
  ``CircuitRecursion.frameOracle,
  ``CircuitRecursion.chartTargetOracle,
  ``CircuitRecursion.chartMassScore,
  ``CircuitRecursion.chooseChart,
  ``CircuitRecursion.residualSmall,
  ``CircuitRecursion.ScalarExpression.executedOperations,
  ``CircuitRecursion.PacketExpression.executedOperations,
  ``CircuitRecursion.ArithmeticWordResult.executedOperations,
  ``CircuitRecursion.expressionPowerTwo,
  ``CircuitRecursion.executeExpressionRoot,
  ``CircuitRecursion.executeStoppingThreshold,
  ``CircuitRecursion.ScalarExpression.run,
  ``CircuitRecursion.PacketExpression.run,
  ``CircuitRecursion.ScalarOperationBound,
  ``CircuitRecursion.PacketOperationBound,
  ``CircuitRecursion.BitEnvelope,
  ``CircuitRecursion.ScalarBitEnvelope,
  ``CircuitRecursion.PacketBitEnvelope,
  ``CircuitRecursion.bitAddEnvelope,
  ``CircuitRecursion.bitMulEnvelope,
  ``CircuitRecursion.bitInvEnvelope,
  ``CircuitRecursion.bitSqrtEnvelope,
  ``CircuitRecursion.bitMeanEnvelope,
  ``CircuitRecursion.bitPacketMulEnvelope,
  ``CircuitRecursion.bitDistanceEnvelope,
  ``CircuitRecursion.bitBalancedSEnvelope,
  ``CircuitRecursion.bitBalancedCEnvelope,
  ``CircuitRecursion.bitReferenceEnvelope,
  ``CircuitRecursion.bitBalancedReferenceEnvelope,
  ``CircuitRecursion.bitChartTargetEnvelope,
  ``CircuitRecursion.bitChartMassEnvelope,
  ``CircuitRecursion.bitRadiusEnvelope,
  ``CircuitRecursion.bitNormalizedEnvelope,
  ``CircuitRecursion.bitConjugatorEnvelope,
  ``CircuitRecursion.bitFactorEnvelope,
  ``CircuitRecursion.expressionBalancedS,
  ``CircuitRecursion.expressionBalancedC,
  ``CircuitRecursion.expressionReferenceX,
  ``CircuitRecursion.expressionReferenceY,
  ``CircuitRecursion.expressionBalancedReference,
  ``CircuitRecursion.expressionChartTarget,
  ``CircuitRecursion.expressionChartMass,
  ``CircuitRecursion.expressionRadius,
  ``CircuitRecursion.expressionNormalized,
  ``CircuitRecursion.expressionConjugator,
  ``CircuitRecursion.expressionConjugate,
  ``CircuitRecursion.expressionFactorX,
  ``CircuitRecursion.expressionFactorY,
  ``CircuitRecursion.cachedPacketExpression,
  ``CircuitRecursion.rationalBinaryExponent,
  ``CircuitRecursion.ScalarExpression.integerBitBudget,
  ``CircuitRecursion.PacketExpression.integerBitBudget,
  ``CircuitRecursion.IntegerScalar.meanMinus,
  ``CircuitRecursion.integerStoppingThreshold,
  ``CircuitRecursion.ScalarExpression.integerRun,
  ``CircuitRecursion.PacketExpression.integerRun,
  ``CircuitRecursion.IntegerPacket.inverse,
  ``CircuitRecursion.IntegerPacket.distanceNumerator,
  ``CircuitRecursion.IntegerPacket.distanceScalar,
  ``CircuitRecursion.IntegerPacket,
  ``CircuitRecursion.IntegerPacket.value,
  ``CircuitRecursion.IntegerPacket.one,
  ``CircuitRecursion.IntegerPacket.mul,
  ``CircuitRecursion.IntegerPacketHeight,
  ``CircuitRecursion.IntegerPacketOracle,
  ``CircuitRecursion.integerPacketOracle,
  ``CircuitRecursion.integerPacketWord,
  ``CircuitRecursion.dyadicIntegerPacket,
  ``CircuitRecursion.cachedIntegerPacket,
  ``CircuitRecursion.IntegerScalar,
  ``CircuitRecursion.IntegerScalar.value,
  ``CircuitRecursion.IntegerScalar.ofInt,
  ``CircuitRecursion.IntegerScalar.add,
  ``CircuitRecursion.IntegerScalar.neg,
  ``CircuitRecursion.IntegerScalar.mul,
  ``CircuitRecursion.IntegerScalar.inv,
  ``CircuitRecursion.IntegerScalarHeight,
  ``CircuitRecursion.IntegerScalar.root,
  ``CircuitRecursion.IntegerScalar.ofRat,
  ``CircuitRecursion.IntegerPacket.coordinate,
  ``CircuitRecursion.IntegerPacket.ofScalars,
  ``CircuitRecursion.IntegerPacket.ofVector,
  ``CircuitRecursion.normalizedQuaternionSU2,
  ``CircuitRecursion.normalizedIntertwiner,
  ``CircuitRecursion.coordinateSubOracle,
  ``CircuitRecursion.intertwinerRadiusOracle,
  ``CircuitRecursion.normalizedIntertwinerOracle,
  ``CircuitRecursion.numericalCorrection,
  ``CircuitRecursion.correctionDemand,
  ``CircuitRecursion.numericalDemand,
  ``CircuitRecursion.correctionOperationSlope,
  ``CircuitRecursion.correctionOperationOffset,
  ``CircuitRecursion.WordOperationBound,
  ``CircuitRecursion.pairOperationSlope,
  ``CircuitRecursion.pairOperationOffset,
  ``CircuitRecursion.numericalThreshold,
  ``CircuitRecursion.numericalPairWord,
  ``CircuitRecursion.slopeGrowth,
  ``CircuitRecursion.offsetGrowth,
  ``CircuitRecursion.AgreesThrough,
  ``CircuitRecursion.expressionWord,
  ``CircuitRecursion.ArithmeticWordResult,
  ``CircuitRecursion.ArithmeticWordResult.operations,
  ``CircuitRecursion.tracedBase,
  ``CircuitRecursion.tracedCorrection,
  ``CircuitRecursion.tracedPairWord,
  ``EffectiveEncoding.AngleAtom.cosOracle,
  ``EffectiveEncoding.AngleAtom.sinOracle,
  ``EffectiveEncoding.AngleCode.cosOracle,
  ``EffectiveEncoding.AngleCode.sinOracle,
  ``EffectiveEncoding.allBranchCode,
  ``EffectiveEncoding.occupationStepCode,
  ``EffectiveEncoding.GateCode.extend,
  ``EffectiveEncoding.prefixCode,
  ``EffectiveEncoding.GateCode.shift,
  ``EffectiveEncoding.shiftCode,
  ``EffectiveEncoding.stageCode,
  ``EffectiveEncoding.stageCircuit,
  ``EffectiveEncoding.compressionCode,
  ``EffectiveEncoding.compressionCircuit,
  ``EffectiveEncoding.AngleCode.Fits,
  ``EffectiveEncoding.SingleCode.Fits,
  ``EffectiveEncoding.SingleCode.inverseDepth,
  ``EffectiveEncoding.GateCode.Fits,
  ``EffectiveEncoding.WordFits,
  ``EffectiveEncoding.RawCode.Fits,
  ``EffectiveEncoding.halvingBudget,
  ``EffectiveEncoding.binaryWidth,
  ``EffectiveEncoding.AngleCode.descriptionWeight,
  ``EffectiveEncoding.angleWeightBudget,
  ``EffectiveEncoding.SingleCode.descriptionWeight,
  ``EffectiveEncoding.GateCode.descriptionWeight,
  ``EffectiveEncoding.codeDescriptionWeight,
  ``EffectiveEncoding.AngleAtom,
  ``EffectiveEncoding.AngleCode,
  ``EffectiveEncoding.AngleAtom.value,
  ``EffectiveEncoding.AngleCode.value,
  ``EffectiveEncoding.AngleCode.neg,
  ``EffectiveEncoding.AngleCode.half,
  ``EffectiveEncoding.piCode,
  ``EffectiveEncoding.SingleCode,
  ``EffectiveEncoding.SingleCode.value,
  ``EffectiveEncoding.GateCode,
  ``EffectiveEncoding.GateCode.value,
  ``EffectiveEncoding.GateCode.inverse,
  ``EffectiveEncoding.WordCode,
  ``EffectiveEncoding.interpret,
  ``EffectiveEncoding.reverseCode,
  ``EffectiveEncoding.maskOfBits,
  ``EffectiveEncoding.masks,
  ``EffectiveEncoding.controls,
  ``EffectiveEncoding.cnotCode,
  ``EffectiveEncoding.parityCode,
  ``EffectiveEncoding.pauliCode,
  ``EffectiveEncoding.signedCode,
  ``EffectiveEncoding.maskParity,
  ``EffectiveEncoding.selectedCode,
  ``EffectiveEncoding.Triple,
  ``EffectiveEncoding.total,
  ``EffectiveEncoding.triples,
  ``EffectiveEncoding.fromTriple,
  ``EffectiveEncoding.toTriple,
  ``EffectiveEncoding.occupations,
  ``EffectiveEncoding.rank,
  ``EffectiveEncoding.unrank,
  ``EffectiveEncoding.rankEquiv,
  ``EffectiveEncoding.boundedBits,
  ``EffectiveEncoding.compactEncoding,
  ``EffectiveEncoding.originalEncoding,
  ``EffectiveEncoding.nextEncoding,
  ``EffectiveEncoding.decode,
  ``EffectiveEncoding.castCode,
  ``EffectiveEncoding.bellPreparationCode,
  ``EffectiveEncoding.bellPairsCode,
  ``EffectiveEncoding.extractionCode,
  ``EffectiveEncoding.extractionCircuit,
  ``EffectiveEncoding.extractionVector,
  ``EffectiveEncoding.garbageVector,
  ``EffectiveEncoding.extractionOutput,
  ``EffectiveEncoding.LabelGate,
  ``EffectiveEncoding.LabelGate.value,
  ``EffectiveEncoding.labelCircuit,
  ``EffectiveEncoding.wireLabels,
  ``EffectiveEncoding.compileLabels,
  ``EffectiveEncoding.compileLabelWord,
  ``EffectiveEncoding.adjacentSwapCode,
  ``EffectiveEncoding.adjacentRotationCode,
  ``EffectiveEncoding.orientedRotationCode,
  ``EffectiveEncoding.otherWires,
  ``EffectiveEncoding.differingWire,
  ``EffectiveEncoding.moveCode,
  ``EffectiveEncoding.swapCode,
  ``EffectiveEncoding.rotationCode,
  ``EffectiveEncoding.GateCode.representative,
  ``EffectiveEncoding.GateCode.globalPhase,
  ``EffectiveEncoding.representativeCircuit,
  ``EffectiveEncoding.wordPhase,
  ``EffectiveEncoding.descriptorSynthesis,
  ``EffectiveEncoding.extractionPrecision,
  ``EffectiveEncoding.numericalExtractionCode,
  ``EffectiveEncoding.descriptorArithmeticOperations,
  ``EffectiveEncoding.gateArithmeticOperations,
  ``EffectiveEncoding.extractionArithmeticOperations,
  ``EffectiveEncoding.countProgram,
  ``EffectiveEncoding.indexedCount,
  ``EffectiveEncoding.explicitOthers,
  ``EffectiveEncoding.integerIndexedCode,
  ``EffectiveEncoding.occupiedPivot,
  ``EffectiveEncoding.branchEmbedding,
  ``EffectiveEncoding.pivotCoordinates,
  ``EffectiveEncoding.pivotEmbedding,
  ``EffectiveEncoding.branchCode,
  ``EffectiveEncoding.RawCode,
  ``EffectiveEncoding.mergeCode,
  ``EffectiveEncoding.RawCode.value,
  ``EffectiveEncoding.RawCode.compile,
  ``EffectiveEncoding.compileRaw,
  ``EffectiveEncoding.alignmentPerm,
  ``EffectiveEncoding.alignmentCode,
  ``EffectiveEncoding.hadRepresentative,
  ``EffectiveEncoding.yRepresentative,
  ``EffectiveEncoding.phaseRepresentative,
  ``EffectiveEncoding.SingleCode.representative,
  ``EffectiveEncoding.SingleCode.globalPhase,
  ``EffectiveEncoding.invSqrtTwoOracle,
  ``EffectiveEncoding.phaseCosOracle,
  ``EffectiveEncoding.phaseSinOracle,
  ``EffectiveEncoding.quaternionStarOracle,
  ``EffectiveEncoding.coordinatePacket,
  ``EffectiveEncoding.SingleCode.quaternionOracle
])

#check CircuitRecursion.expressionAdd_eval
set_option pp.universes false in #print axioms CircuitRecursion.expressionAdd_eval
#check CircuitRecursion.expressionNeg_eval
set_option pp.universes false in #print axioms CircuitRecursion.expressionNeg_eval
#check CircuitRecursion.expressionMul_eval
set_option pp.universes false in #print axioms CircuitRecursion.expressionMul_eval
#check CircuitRecursion.expressionInv_eval
set_option pp.universes false in #print axioms CircuitRecursion.expressionInv_eval
#check CircuitRecursion.expressionSqrt_eval
set_option pp.universes false in #print axioms CircuitRecursion.expressionSqrt_eval
#check CircuitRecursion.expressionMeanMinus_eval
set_option pp.universes false in #print axioms CircuitRecursion.expressionMeanMinus_eval
#check CircuitRecursion.expressionCoordinate_eval
set_option pp.universes false in #print axioms CircuitRecursion.expressionCoordinate_eval
#check CircuitRecursion.expressionPacketMul_eval
set_option pp.universes false in #print axioms CircuitRecursion.expressionPacketMul_eval
#check CircuitRecursion.expressionPacketInverse_eval
set_option pp.universes false in #print axioms CircuitRecursion.expressionPacketInverse_eval
#check CircuitRecursion.expressionPacketOne_eval
set_option pp.universes false in #print axioms CircuitRecursion.expressionPacketOne_eval
#check CircuitRecursion.expressionFrame_eval
set_option pp.universes false in #print axioms CircuitRecursion.expressionFrame_eval
#check CircuitRecursion.expressionDistance_eval
set_option pp.universes false in #print axioms CircuitRecursion.expressionDistance_eval
#check CircuitRecursion.balancedParameterFacts
set_option pp.universes false in #print axioms CircuitRecursion.balancedParameterFacts
#check CircuitRecursion.balancedCircle
set_option pp.universes false in #print axioms CircuitRecursion.balancedCircle
#check CircuitRecursion.balancedReference_scalar
set_option pp.universes false in #print axioms CircuitRecursion.balancedReference_scalar
#check CircuitRecursion.referenceX_distance
set_option pp.universes false in #print axioms CircuitRecursion.referenceX_distance
#check CircuitRecursion.referenceY_distance
set_option pp.universes false in #print axioms CircuitRecursion.referenceY_distance
#check CircuitRecursion.coordinateOracle_correct
set_option pp.universes false in #print axioms CircuitRecursion.coordinateOracle_correct
#check CircuitRecursion.balancedSOracle_correct
set_option pp.universes false in #print axioms CircuitRecursion.balancedSOracle_correct
#check CircuitRecursion.balancedCOracle_correct
set_option pp.universes false in #print axioms CircuitRecursion.balancedCOracle_correct
#check CircuitRecursion.referenceXOracle_correct
set_option pp.universes false in #print axioms CircuitRecursion.referenceXOracle_correct
#check CircuitRecursion.referenceYOracle_correct
set_option pp.universes false in #print axioms CircuitRecursion.referenceYOracle_correct
#check CircuitRecursion.balancedReferenceOracle_correct
set_option pp.universes false in #print axioms CircuitRecursion.balancedReferenceOracle_correct
#check CircuitRecursion.cachedNumericalRun_query_bounds
set_option pp.universes false in #print axioms CircuitRecursion.cachedNumericalRun_query_bounds
#check CircuitRecursion.cachedNumericalRun_precision_bounds
set_option pp.universes false in #print axioms CircuitRecursion.cachedNumericalRun_precision_bounds
#check CircuitRecursion.dyadic_numerator_bits
set_option pp.universes false in #print axioms CircuitRecursion.dyadic_numerator_bits
#check CircuitRecursion.dyadicPacketBits_bound
set_option pp.universes false in #print axioms CircuitRecursion.dyadicPacketBits_bound
#check CircuitRecursion.cachedInputBits_bound
set_option pp.universes false in #print axioms CircuitRecursion.cachedInputBits_bound
#check CircuitRecursion.cachedInputBits_precision_bound
set_option pp.universes false in #print axioms CircuitRecursion.cachedInputBits_precision_bound
#check CircuitRecursion.cachedArithmeticRun_word
set_option pp.universes false in #print axioms CircuitRecursion.cachedArithmeticRun_word
#check CircuitRecursion.cachedArithmeticRun_operations
set_option pp.universes false in #print axioms CircuitRecursion.cachedArithmeticRun_operations
#check CircuitRecursion.cachedArithmeticRun_executedOperations
set_option pp.universes false in #print axioms CircuitRecursion.cachedArithmeticRun_executedOperations
#check CircuitRecursion.cachedArithmeticSU2Synthesis
set_option pp.universes false in #print axioms CircuitRecursion.cachedArithmeticSU2Synthesis
#check CircuitRecursion.buildPacketCache_agrees
set_option pp.universes false in #print axioms CircuitRecursion.buildPacketCache_agrees
#check CircuitRecursion.buildPacketCache_requests
set_option pp.universes false in #print axioms CircuitRecursion.buildPacketCache_requests
#check CircuitRecursion.buildPacketCache_precision
set_option pp.universes false in #print axioms CircuitRecursion.buildPacketCache_precision
#check CircuitRecursion.cachedNumericalRun_word
set_option pp.universes false in #print axioms CircuitRecursion.cachedNumericalRun_word
#check CircuitRecursion.cachedNumericalRun_gateRequests
set_option pp.universes false in #print axioms CircuitRecursion.cachedNumericalRun_gateRequests
#check CircuitRecursion.cachedNumericalRun_targetRequests
set_option pp.universes false in #print axioms CircuitRecursion.cachedNumericalRun_targetRequests
#check CircuitRecursion.cachedNumericalRun_gatePrecision
set_option pp.universes false in #print axioms CircuitRecursion.cachedNumericalRun_gatePrecision
#check CircuitRecursion.cachedNumericalRun_targetPrecision
set_option pp.universes false in #print axioms CircuitRecursion.cachedNumericalRun_targetPrecision
#check CircuitRecursion.cachedNumericalSU2Synthesis
set_option pp.universes false in #print axioms CircuitRecursion.cachedNumericalSU2Synthesis
#check CircuitRecursion.quaternionConjugateOracle_correct
set_option pp.universes false in #print axioms CircuitRecursion.quaternionConjugateOracle_correct
#check CircuitRecursion.conditionedFactors_correct
set_option pp.universes false in #print axioms CircuitRecursion.conditionedFactors_correct
#check CircuitRecursion.quaternionCoordinates_inverse
set_option pp.universes false in #print axioms CircuitRecursion.quaternionCoordinates_inverse
#check CircuitRecursion.quaternionOracleInverse_correct
set_option pp.universes false in #print axioms CircuitRecursion.quaternionOracleInverse_correct
#check CircuitRecursion.frameOracle_correct
set_option pp.universes false in #print axioms CircuitRecursion.frameOracle_correct
#check CircuitRecursion.chartTargetOracle_correct
set_option pp.universes false in #print axioms CircuitRecursion.chartTargetOracle_correct
#check CircuitRecursion.intertwinerMass_distance
set_option pp.universes false in #print axioms CircuitRecursion.intertwinerMass_distance
#check CircuitRecursion.chartMassScore_correct
set_option pp.universes false in #print axioms CircuitRecursion.chartMassScore_correct
#check CircuitRecursion.dyadic_square_precision
set_option pp.universes false in #print axioms CircuitRecursion.dyadic_square_precision
#check CircuitRecursion.chooseChart_denominator
set_option pp.universes false in #print axioms CircuitRecursion.chooseChart_denominator
#check CircuitRecursion.residualSmall_correct
set_option pp.universes false in #print axioms CircuitRecursion.residualSmall_correct
#check CircuitRecursion.ScalarExpression.executedOperations_le
set_option pp.universes false in #print axioms CircuitRecursion.ScalarExpression.executedOperations_le
#check CircuitRecursion.PacketExpression.executedOperations_le
set_option pp.universes false in #print axioms CircuitRecursion.PacketExpression.executedOperations_le
#check CircuitRecursion.ArithmeticWordResult.executedOperations_le
set_option pp.universes false in #print axioms CircuitRecursion.ArithmeticWordResult.executedOperations_le
#check CircuitRecursion.expressionPowerTwo_eq
set_option pp.universes false in #print axioms CircuitRecursion.expressionPowerTwo_eq
#check CircuitRecursion.executeExpressionRoot_correct
set_option pp.universes false in #print axioms CircuitRecursion.executeExpressionRoot_correct
#check CircuitRecursion.executeStoppingThreshold_correct
set_option pp.universes false in #print axioms CircuitRecursion.executeStoppingThreshold_correct
#check CircuitRecursion.ScalarExpression.run_correct
set_option pp.universes false in #print axioms CircuitRecursion.ScalarExpression.run_correct
#check CircuitRecursion.PacketExpression.run_correct
set_option pp.universes false in #print axioms CircuitRecursion.PacketExpression.run_correct
#check CircuitRecursion.expressionAdd_bound
set_option pp.universes false in #print axioms CircuitRecursion.expressionAdd_bound
#check CircuitRecursion.expressionNeg_bound
set_option pp.universes false in #print axioms CircuitRecursion.expressionNeg_bound
#check CircuitRecursion.expressionMul_bound
set_option pp.universes false in #print axioms CircuitRecursion.expressionMul_bound
#check CircuitRecursion.expressionInv_bound
set_option pp.universes false in #print axioms CircuitRecursion.expressionInv_bound
#check CircuitRecursion.expressionSqrt_bound
set_option pp.universes false in #print axioms CircuitRecursion.expressionSqrt_bound
#check CircuitRecursion.expressionMeanMinus_bound
set_option pp.universes false in #print axioms CircuitRecursion.expressionMeanMinus_bound
#check CircuitRecursion.expressionCoordinate_bound
set_option pp.universes false in #print axioms CircuitRecursion.expressionCoordinate_bound
#check CircuitRecursion.expressionPacketMul_bound
set_option pp.universes false in #print axioms CircuitRecursion.expressionPacketMul_bound
#check CircuitRecursion.expressionPacketInverse_bound
set_option pp.universes false in #print axioms CircuitRecursion.expressionPacketInverse_bound
#check CircuitRecursion.expressionDistance_bound
set_option pp.universes false in #print axioms CircuitRecursion.expressionDistance_bound
#check CircuitRecursion.expressionBalancedS_bound
set_option pp.universes false in #print axioms CircuitRecursion.expressionBalancedS_bound
#check CircuitRecursion.expressionBalancedC_bound
set_option pp.universes false in #print axioms CircuitRecursion.expressionBalancedC_bound
#check CircuitRecursion.expressionReferenceX_bound
set_option pp.universes false in #print axioms CircuitRecursion.expressionReferenceX_bound
#check CircuitRecursion.expressionReferenceY_bound
set_option pp.universes false in #print axioms CircuitRecursion.expressionReferenceY_bound
#check CircuitRecursion.expressionBalancedReference_bound
set_option pp.universes false in #print axioms CircuitRecursion.expressionBalancedReference_bound
#check CircuitRecursion.expressionChartTarget_bound
set_option pp.universes false in #print axioms CircuitRecursion.expressionChartTarget_bound
#check CircuitRecursion.expressionChartMass_bound
set_option pp.universes false in #print axioms CircuitRecursion.expressionChartMass_bound
#check CircuitRecursion.expressionNormalized_bound
set_option pp.universes false in #print axioms CircuitRecursion.expressionNormalized_bound
#check CircuitRecursion.expressionConjugator_bound
set_option pp.universes false in #print axioms CircuitRecursion.expressionConjugator_bound
#check CircuitRecursion.expressionFactor_bounds
set_option pp.universes false in #print axioms CircuitRecursion.expressionFactor_bounds
#check CircuitRecursion.bitAdd_bound
set_option pp.universes false in #print axioms CircuitRecursion.bitAdd_bound
#check CircuitRecursion.bitNeg_bound
set_option pp.universes false in #print axioms CircuitRecursion.bitNeg_bound
#check CircuitRecursion.bitMul_bound
set_option pp.universes false in #print axioms CircuitRecursion.bitMul_bound
#check CircuitRecursion.bitInv_bound
set_option pp.universes false in #print axioms CircuitRecursion.bitInv_bound
#check CircuitRecursion.bitSqrt_bound
set_option pp.universes false in #print axioms CircuitRecursion.bitSqrt_bound
#check CircuitRecursion.bitMean_bound
set_option pp.universes false in #print axioms CircuitRecursion.bitMean_bound
#check CircuitRecursion.bitCoordinate_bound
set_option pp.universes false in #print axioms CircuitRecursion.bitCoordinate_bound
#check CircuitRecursion.bitPacketMul_bound
set_option pp.universes false in #print axioms CircuitRecursion.bitPacketMul_bound
#check CircuitRecursion.bitPacketInverse_bound
set_option pp.universes false in #print axioms CircuitRecursion.bitPacketInverse_bound
#check CircuitRecursion.bitDistance_bound
set_option pp.universes false in #print axioms CircuitRecursion.bitDistance_bound
#check CircuitRecursion.rationalBinaryExponent_zero
set_option pp.universes false in #print axioms CircuitRecursion.rationalBinaryExponent_zero
#check CircuitRecursion.rationalBinaryExponent_one
set_option pp.universes false in #print axioms CircuitRecursion.rationalBinaryExponent_one
#check CircuitRecursion.bitFrame_bound
set_option pp.universes false in #print axioms CircuitRecursion.bitFrame_bound
#check CircuitRecursion.bitBalancedS_bound
set_option pp.universes false in #print axioms CircuitRecursion.bitBalancedS_bound
#check CircuitRecursion.bitBalancedC_bound
set_option pp.universes false in #print axioms CircuitRecursion.bitBalancedC_bound
#check CircuitRecursion.bitReference_bounds
set_option pp.universes false in #print axioms CircuitRecursion.bitReference_bounds
#check CircuitRecursion.bitBalancedReference_bound
set_option pp.universes false in #print axioms CircuitRecursion.bitBalancedReference_bound
#check CircuitRecursion.bitChartTarget_bound
set_option pp.universes false in #print axioms CircuitRecursion.bitChartTarget_bound
#check CircuitRecursion.bitChartMass_bound
set_option pp.universes false in #print axioms CircuitRecursion.bitChartMass_bound
#check CircuitRecursion.bitNormalized_bound
set_option pp.universes false in #print axioms CircuitRecursion.bitNormalized_bound
#check CircuitRecursion.bitConjugator_bound
set_option pp.universes false in #print axioms CircuitRecursion.bitConjugator_bound
#check CircuitRecursion.bitFactor_bounds
set_option pp.universes false in #print axioms CircuitRecursion.bitFactor_bounds
#check CircuitRecursion.fixedFactor_integerBitBudget
set_option pp.universes false in #print axioms CircuitRecursion.fixedFactor_integerBitBudget
#check CircuitRecursion.chooseChart_agrees
set_option pp.universes false in #print axioms CircuitRecursion.chooseChart_agrees
#check CircuitRecursion.coordinateSubOracle_agrees
set_option pp.universes false in #print axioms CircuitRecursion.coordinateSubOracle_agrees
#check CircuitRecursion.intertwinerRadiusOracle_agrees
set_option pp.universes false in #print axioms CircuitRecursion.intertwinerRadiusOracle_agrees
#check CircuitRecursion.normalizedIntertwinerOracle_agrees
set_option pp.universes false in #print axioms CircuitRecursion.normalizedIntertwinerOracle_agrees
#check CircuitRecursion.conditionedConjugatorOracle_agrees
set_option pp.universes false in #print axioms CircuitRecursion.conditionedConjugatorOracle_agrees
#check CircuitRecursion.conditionedFactorXOracle_agrees
set_option pp.universes false in #print axioms CircuitRecursion.conditionedFactorXOracle_agrees
#check CircuitRecursion.conditionedFactorYOracle_agrees
set_option pp.universes false in #print axioms CircuitRecursion.conditionedFactorYOracle_agrees
#check CircuitRecursion.expressionBalancedS_eval
set_option pp.universes false in #print axioms CircuitRecursion.expressionBalancedS_eval
#check CircuitRecursion.expressionBalancedC_eval
set_option pp.universes false in #print axioms CircuitRecursion.expressionBalancedC_eval
#check CircuitRecursion.expressionReferenceX_eval
set_option pp.universes false in #print axioms CircuitRecursion.expressionReferenceX_eval
#check CircuitRecursion.expressionReferenceY_eval
set_option pp.universes false in #print axioms CircuitRecursion.expressionReferenceY_eval
#check CircuitRecursion.expressionBalancedReference_eval
set_option pp.universes false in #print axioms CircuitRecursion.expressionBalancedReference_eval
#check CircuitRecursion.expressionChartTarget_eval
set_option pp.universes false in #print axioms CircuitRecursion.expressionChartTarget_eval
#check CircuitRecursion.expressionChartMass_eval
set_option pp.universes false in #print axioms CircuitRecursion.expressionChartMass_eval
#check CircuitRecursion.expressionRadius_eval
set_option pp.universes false in #print axioms CircuitRecursion.expressionRadius_eval
#check CircuitRecursion.expressionNormalized_eval
set_option pp.universes false in #print axioms CircuitRecursion.expressionNormalized_eval
#check CircuitRecursion.expressionConjugator_eval
set_option pp.universes false in #print axioms CircuitRecursion.expressionConjugator_eval
#check CircuitRecursion.expressionConjugate_eval
set_option pp.universes false in #print axioms CircuitRecursion.expressionConjugate_eval
#check CircuitRecursion.expressionFactorX_eval
set_option pp.universes false in #print axioms CircuitRecursion.expressionFactorX_eval
#check CircuitRecursion.expressionFactorY_eval
set_option pp.universes false in #print axioms CircuitRecursion.expressionFactorY_eval
#check CircuitRecursion.cachedPacketExpression_bitEnvelope
set_option pp.universes false in #print axioms CircuitRecursion.cachedPacketExpression_bitEnvelope
#check CircuitRecursion.expressionPacketOne_bitEnvelope
set_option pp.universes false in #print axioms CircuitRecursion.expressionPacketOne_bitEnvelope
#check CircuitRecursion.expressionWord_bitEnvelope
set_option pp.universes false in #print axioms CircuitRecursion.expressionWord_bitEnvelope
#check CircuitRecursion.residual_bitEnvelope
set_option pp.universes false in #print axioms CircuitRecursion.residual_bitEnvelope
#check CircuitRecursion.cachedResidualFactor_integerHeight
set_option pp.universes false in #print axioms CircuitRecursion.cachedResidualFactor_integerHeight
#check CircuitRecursion.rationalBinaryExponent_height
set_option pp.universes false in #print axioms CircuitRecursion.rationalBinaryExponent_height
#check CircuitRecursion.rationalBinaryExponent_le
set_option pp.universes false in #print axioms CircuitRecursion.rationalBinaryExponent_le
#check CircuitRecursion.ScalarExpression.integerRun_height
set_option pp.universes false in #print axioms CircuitRecursion.ScalarExpression.integerRun_height
#check CircuitRecursion.PacketExpression.integerRun_height
set_option pp.universes false in #print axioms CircuitRecursion.PacketExpression.integerRun_height
#check CircuitRecursion.IntegerScalar.meanMinus_value
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalar.meanMinus_value
#check CircuitRecursion.IntegerScalarHeight.mono
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalarHeight.mono
#check CircuitRecursion.IntegerScalar.meanMinus_height
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalar.meanMinus_height
#check CircuitRecursion.integerStoppingThreshold_value
set_option pp.universes false in #print axioms CircuitRecursion.integerStoppingThreshold_value
#check CircuitRecursion.rationalSqrtApprox_max
set_option pp.universes false in #print axioms CircuitRecursion.rationalSqrtApprox_max
#check CircuitRecursion.ScalarExpression.integerRun_correct
set_option pp.universes false in #print axioms CircuitRecursion.ScalarExpression.integerRun_correct
#check CircuitRecursion.PacketExpression.integerRun_correct
set_option pp.universes false in #print axioms CircuitRecursion.PacketExpression.integerRun_correct
#check CircuitRecursion.IntegerPacket.inverse_value
set_option pp.universes false in #print axioms CircuitRecursion.IntegerPacket.inverse_value
#check CircuitRecursion.IntegerPacket.inverse_height
set_option pp.universes false in #print axioms CircuitRecursion.IntegerPacket.inverse_height
#check CircuitRecursion.IntegerPacket.distanceScalar_value
set_option pp.universes false in #print axioms CircuitRecursion.IntegerPacket.distanceScalar_value
#check CircuitRecursion.IntegerPacket.distanceNumerator_bound
set_option pp.universes false in #print axioms CircuitRecursion.IntegerPacket.distanceNumerator_bound
#check CircuitRecursion.IntegerPacket.distanceScalar_height
set_option pp.universes false in #print axioms CircuitRecursion.IntegerPacket.distanceScalar_height
#check CircuitRecursion.IntegerPacket.mul_value
set_option pp.universes false in #print axioms CircuitRecursion.IntegerPacket.mul_value
#check CircuitRecursion.quaternionSign_natAbs
set_option pp.universes false in #print axioms CircuitRecursion.quaternionSign_natAbs
#check CircuitRecursion.integerQuaternionProduct_bound
set_option pp.universes false in #print axioms CircuitRecursion.integerQuaternionProduct_bound
#check CircuitRecursion.IntegerPacketHeight.mono
set_option pp.universes false in #print axioms CircuitRecursion.IntegerPacketHeight.mono
#check CircuitRecursion.IntegerPacket.one_height
set_option pp.universes false in #print axioms CircuitRecursion.IntegerPacket.one_height
#check CircuitRecursion.IntegerPacket.mul_height
set_option pp.universes false in #print axioms CircuitRecursion.IntegerPacket.mul_height
#check CircuitRecursion.integerPacketWord_value
set_option pp.universes false in #print axioms CircuitRecursion.integerPacketWord_value
#check CircuitRecursion.integerPacketWord_height
set_option pp.universes false in #print axioms CircuitRecursion.integerPacketWord_height
#check CircuitRecursion.dyadicIntegerPacket_value
set_option pp.universes false in #print axioms CircuitRecursion.dyadicIntegerPacket_value
#check CircuitRecursion.dyadicIntegerPacket_height
set_option pp.universes false in #print axioms CircuitRecursion.dyadicIntegerPacket_height
#check CircuitRecursion.IntegerPacket.one_value
set_option pp.universes false in #print axioms CircuitRecursion.IntegerPacket.one_value
#check CircuitRecursion.cachedIntegerPacket_value
set_option pp.universes false in #print axioms CircuitRecursion.cachedIntegerPacket_value
#check CircuitRecursion.cachedIntegerPacket_height
set_option pp.universes false in #print axioms CircuitRecursion.cachedIntegerPacket_height
#check CircuitRecursion.cachedIntegerPacketWord_height
set_option pp.universes false in #print axioms CircuitRecursion.cachedIntegerPacketWord_height
#check CircuitRecursion.cachedIntegerPacketWord_value
set_option pp.universes false in #print axioms CircuitRecursion.cachedIntegerPacketWord_value
#check CircuitRecursion.commonDenominator_binary_bound
set_option pp.universes false in #print axioms CircuitRecursion.commonDenominator_binary_bound
#check CircuitRecursion.IntegerPacketHeight.binary_bounds
set_option pp.universes false in #print axioms CircuitRecursion.IntegerPacketHeight.binary_bounds
#check CircuitRecursion.cachedSynthesisWord_integerHeight
set_option pp.universes false in #print axioms CircuitRecursion.cachedSynthesisWord_integerHeight
#check CircuitRecursion.IntegerScalar.add_value
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalar.add_value
#check CircuitRecursion.IntegerScalar.neg_value
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalar.neg_value
#check CircuitRecursion.IntegerScalar.mul_value
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalar.mul_value
#check CircuitRecursion.IntegerScalar.inv_value
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalar.inv_value
#check CircuitRecursion.IntegerScalar.add_height
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalar.add_height
#check CircuitRecursion.IntegerScalar.neg_height
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalar.neg_height
#check CircuitRecursion.IntegerScalar.mul_height
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalar.mul_height
#check CircuitRecursion.IntegerScalar.inv_height
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalar.inv_height
#check CircuitRecursion.IntegerScalar.max_value
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalar.max_value
#check CircuitRecursion.IntegerScalar.root_value
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalar.root_value
#check CircuitRecursion.IntegerScalar.root_height
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalar.root_height
#check CircuitRecursion.IntegerScalar.ofRat_value
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalar.ofRat_value
#check CircuitRecursion.IntegerScalar.canonical_height
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalar.canonical_height
#check CircuitRecursion.IntegerPacket.coordinate_value
set_option pp.universes false in #print axioms CircuitRecursion.IntegerPacket.coordinate_value
#check CircuitRecursion.IntegerPacket.coordinate_height
set_option pp.universes false in #print axioms CircuitRecursion.IntegerPacket.coordinate_height
#check CircuitRecursion.IntegerPacket.ofScalars_value
set_option pp.universes false in #print axioms CircuitRecursion.IntegerPacket.ofScalars_value
#check CircuitRecursion.product_denominator_bound
set_option pp.universes false in #print axioms CircuitRecursion.product_denominator_bound
#check CircuitRecursion.IntegerPacket.ofScalars_height
set_option pp.universes false in #print axioms CircuitRecursion.IntegerPacket.ofScalars_height
#check CircuitRecursion.IntegerPacket.ofVector_value
set_option pp.universes false in #print axioms CircuitRecursion.IntegerPacket.ofVector_value
#check CircuitRecursion.IntegerPacket.ofVector_height
set_option pp.universes false in #print axioms CircuitRecursion.IntegerPacket.ofVector_height
#check CircuitRecursion.normalizedQuaternionSU2_unitary
set_option pp.universes false in #print axioms CircuitRecursion.normalizedQuaternionSU2_unitary
#check CircuitRecursion.normalizedIntertwiner_coordinates
set_option pp.universes false in #print axioms CircuitRecursion.normalizedIntertwiner_coordinates
#check CircuitRecursion.coordinateSubOracle_correct
set_option pp.universes false in #print axioms CircuitRecursion.coordinateSubOracle_correct
#check CircuitRecursion.normalizedIntertwinerOracle_correct
set_option pp.universes false in #print axioms CircuitRecursion.normalizedIntertwinerOracle_correct
#check CircuitRecursion.numericalCorrection_length
set_option pp.universes false in #print axioms CircuitRecursion.numericalCorrection_length
#check CircuitRecursion.numericalCorrection_error
set_option pp.universes false in #print axioms CircuitRecursion.numericalCorrection_error
#check CircuitRecursion.quaternionWordOracle_agrees
set_option pp.universes false in #print axioms CircuitRecursion.quaternionWordOracle_agrees
#check CircuitRecursion.fixedNetWord_agrees
set_option pp.universes false in #print axioms CircuitRecursion.fixedNetWord_agrees
#check CircuitRecursion.residualSmall_agrees
set_option pp.universes false in #print axioms CircuitRecursion.residualSmall_agrees
#check CircuitRecursion.correctionDemand_ge
set_option pp.universes false in #print axioms CircuitRecursion.correctionDemand_ge
#check CircuitRecursion.numericalCorrection_agrees
set_option pp.universes false in #print axioms CircuitRecursion.numericalCorrection_agrees
#check CircuitRecursion.numericalDemand_ge
set_option pp.universes false in #print axioms CircuitRecursion.numericalDemand_ge
#check CircuitRecursion.numericalPairWord_agrees
set_option pp.universes false in #print axioms CircuitRecursion.numericalPairWord_agrees
#check CircuitRecursion.numericalDemand_succ
set_option pp.universes false in #print axioms CircuitRecursion.numericalDemand_succ
#check CircuitRecursion.numericalDemand_bound
set_option pp.universes false in #print axioms CircuitRecursion.numericalDemand_bound
#check CircuitRecursion.numericalDemand_precision_bound
set_option pp.universes false in #print axioms CircuitRecursion.numericalDemand_precision_bound
#check CircuitRecursion.expressionWord_bound
set_option pp.universes false in #print axioms CircuitRecursion.expressionWord_bound
#check CircuitRecursion.tracedBase_operations
set_option pp.universes false in #print axioms CircuitRecursion.tracedBase_operations
#check CircuitRecursion.tracedCorrection_operations
set_option pp.universes false in #print axioms CircuitRecursion.tracedCorrection_operations
#check CircuitRecursion.tracedPairWord_operations
set_option pp.universes false in #print axioms CircuitRecursion.tracedPairWord_operations
#check CircuitRecursion.numerical_stop_budget
set_option pp.universes false in #print axioms CircuitRecursion.numerical_stop_budget
#check CircuitRecursion.numericalDoubleCorrection_error
set_option pp.universes false in #print axioms CircuitRecursion.numericalDoubleCorrection_error
#check CircuitRecursion.numericalThreshold_error
set_option pp.universes false in #print axioms CircuitRecursion.numericalThreshold_error
#check CircuitRecursion.numericalThreshold_depth_bound
set_option pp.universes false in #print axioms CircuitRecursion.numericalThreshold_depth_bound
#check CircuitRecursion.numericalPairWord_error
set_option pp.universes false in #print axioms CircuitRecursion.numericalPairWord_error
#check CircuitRecursion.numericalPairWord_length
set_option pp.universes false in #print axioms CircuitRecursion.numericalPairWord_length
#check CircuitRecursion.numericalSU2Synthesis
set_option pp.universes false in #print axioms CircuitRecursion.numericalSU2Synthesis
#check CircuitRecursion.numericalSU2Synthesis_dyadic
set_option pp.universes false in #print axioms CircuitRecursion.numericalSU2Synthesis_dyadic
#check CircuitRecursion.pairOperationSlope_pos
set_option pp.universes false in #print axioms CircuitRecursion.pairOperationSlope_pos
#check CircuitRecursion.pairOperationSlope_bound
set_option pp.universes false in #print axioms CircuitRecursion.pairOperationSlope_bound
#check CircuitRecursion.pairOperationSlope_length_bound
set_option pp.universes false in #print axioms CircuitRecursion.pairOperationSlope_length_bound
#check CircuitRecursion.pairedOffset_step_bound
set_option pp.universes false in #print axioms CircuitRecursion.pairedOffset_step_bound
#check CircuitRecursion.pairOperationOffset_bound
set_option pp.universes false in #print axioms CircuitRecursion.pairOperationOffset_bound
#check CircuitRecursion.tracedPairWord_literal_operations
set_option pp.universes false in #print axioms CircuitRecursion.tracedPairWord_literal_operations
#check CircuitRecursion.offsetGrowth_precision_bound
set_option pp.universes false in #print axioms CircuitRecursion.offsetGrowth_precision_bound
#check CircuitRecursion.AgreesThrough.mono
set_option pp.universes false in #print axioms CircuitRecursion.AgreesThrough.mono
#check CircuitRecursion.AgreesThrough.refl
set_option pp.universes false in #print axioms CircuitRecursion.AgreesThrough.refl
#check CircuitRecursion.oracleAdd_agrees
set_option pp.universes false in #print axioms CircuitRecursion.oracleAdd_agrees
#check CircuitRecursion.oracleNeg_agrees
set_option pp.universes false in #print axioms CircuitRecursion.oracleNeg_agrees
#check CircuitRecursion.oracleMul_agrees
set_option pp.universes false in #print axioms CircuitRecursion.oracleMul_agrees
#check CircuitRecursion.oracleInv_agrees
set_option pp.universes false in #print axioms CircuitRecursion.oracleInv_agrees
#check CircuitRecursion.oracleSqrt_agrees
set_option pp.universes false in #print axioms CircuitRecursion.oracleSqrt_agrees
#check CircuitRecursion.oracleMeanMinus_agrees
set_option pp.universes false in #print axioms CircuitRecursion.oracleMeanMinus_agrees
#check CircuitRecursion.coordinateOracle_agrees
set_option pp.universes false in #print axioms CircuitRecursion.coordinateOracle_agrees
#check CircuitRecursion.quaternionOracleMul_agrees
set_option pp.universes false in #print axioms CircuitRecursion.quaternionOracleMul_agrees
#check CircuitRecursion.quaternionOracleInverse_agrees
set_option pp.universes false in #print axioms CircuitRecursion.quaternionOracleInverse_agrees
#check CircuitRecursion.quaternionConjugateOracle_agrees
set_option pp.universes false in #print axioms CircuitRecursion.quaternionConjugateOracle_agrees
#check CircuitRecursion.balancedSOracle_agrees
set_option pp.universes false in #print axioms CircuitRecursion.balancedSOracle_agrees
#check CircuitRecursion.balancedCOracle_agrees
set_option pp.universes false in #print axioms CircuitRecursion.balancedCOracle_agrees
#check CircuitRecursion.referenceXOracle_agrees
set_option pp.universes false in #print axioms CircuitRecursion.referenceXOracle_agrees
#check CircuitRecursion.referenceYOracle_agrees
set_option pp.universes false in #print axioms CircuitRecursion.referenceYOracle_agrees
#check CircuitRecursion.balancedReferenceOracle_agrees
set_option pp.universes false in #print axioms CircuitRecursion.balancedReferenceOracle_agrees
#check CircuitRecursion.chartTargetOracle_agrees
set_option pp.universes false in #print axioms CircuitRecursion.chartTargetOracle_agrees
#check CircuitRecursion.distanceScore_agrees
set_option pp.universes false in #print axioms CircuitRecursion.distanceScore_agrees
#check CircuitRecursion.chartMassScore_agrees
set_option pp.universes false in #print axioms CircuitRecursion.chartMassScore_agrees
#check CircuitRecursion.expressionWord_eval
set_option pp.universes false in #print axioms CircuitRecursion.expressionWord_eval
#check CircuitRecursion.tracedBase_word
set_option pp.universes false in #print axioms CircuitRecursion.tracedBase_word
#check CircuitRecursion.tracedCorrection_word
set_option pp.universes false in #print axioms CircuitRecursion.tracedCorrection_word
#check CircuitRecursion.tracedPairWord_word
set_option pp.universes false in #print axioms CircuitRecursion.tracedPairWord_word
#check EffectiveEncoding.mergeAngle_degenerate
set_option pp.universes false in #print axioms EffectiveEncoding.mergeAngle_degenerate
#check EffectiveEncoding.AngleAtom.cosOracle_correct
set_option pp.universes false in #print axioms EffectiveEncoding.AngleAtom.cosOracle_correct
#check EffectiveEncoding.AngleAtom.sinOracle_correct
set_option pp.universes false in #print axioms EffectiveEncoding.AngleAtom.sinOracle_correct
#check EffectiveEncoding.AngleAtom.value_bounds
set_option pp.universes false in #print axioms EffectiveEncoding.AngleAtom.value_bounds
#check EffectiveEncoding.AngleCode.cosOracle_correct
set_option pp.universes false in #print axioms EffectiveEncoding.AngleCode.cosOracle_correct
#check EffectiveEncoding.AngleCode.sinOracle_correct
set_option pp.universes false in #print axioms EffectiveEncoding.AngleCode.sinOracle_correct
#check EffectiveEncoding.AngleCode.evaluation
set_option pp.universes false in #print axioms EffectiveEncoding.AngleCode.evaluation
#check EffectiveEncoding.interpret_flatMap
set_option pp.universes false in #print axioms EffectiveEncoding.interpret_flatMap
#check EffectiveEncoding.allBranchCode_action
set_option pp.universes false in #print axioms EffectiveEncoding.allBranchCode_action
#check EffectiveEncoding.allBranchCode_length
set_option pp.universes false in #print axioms EffectiveEncoding.allBranchCode_length
#check EffectiveEncoding.occupationStepCode_action
set_option pp.universes false in #print axioms EffectiveEncoding.occupationStepCode_action
#check EffectiveEncoding.occupationStepCode_length
set_option pp.universes false in #print axioms EffectiveEncoding.occupationStepCode_length
#check EffectiveEncoding.prefixCode_length
set_option pp.universes false in #print axioms EffectiveEncoding.prefixCode_length
#check EffectiveEncoding.interpret_prefix
set_option pp.universes false in #print axioms EffectiveEncoding.interpret_prefix
#check EffectiveEncoding.shiftCode_length
set_option pp.universes false in #print axioms EffectiveEncoding.shiftCode_length
#check EffectiveEncoding.interpret_shift
set_option pp.universes false in #print axioms EffectiveEncoding.interpret_shift
#check EffectiveEncoding.stageCircuit_action
set_option pp.universes false in #print axioms EffectiveEncoding.stageCircuit_action
#check EffectiveEncoding.compressionCircuit_succ
set_option pp.universes false in #print axioms EffectiveEncoding.compressionCircuit_succ
#check EffectiveEncoding.bitOccupation_zero
set_option pp.universes false in #print axioms EffectiveEncoding.bitOccupation_zero
#check EffectiveEncoding.compressionCircuit_action
set_option pp.universes false in #print axioms EffectiveEncoding.compressionCircuit_action
#check EffectiveEncoding.stageCode_length
set_option pp.universes false in #print axioms EffectiveEncoding.stageCode_length
#check EffectiveEncoding.compressionCode_length
set_option pp.universes false in #print axioms EffectiveEncoding.compressionCode_length
#check EffectiveEncoding.compressionCircuit_matrix
set_option pp.universes false in #print axioms EffectiveEncoding.compressionCircuit_matrix
#check EffectiveEncoding.compressionCircuit_coherent
set_option pp.universes false in #print axioms EffectiveEncoding.compressionCircuit_coherent
#check EffectiveEncoding.compressionCircuit_purePower
set_option pp.universes false in #print axioms EffectiveEncoding.compressionCircuit_purePower
#check EffectiveEncoding.AngleCode.Fits.mono
set_option pp.universes false in #print axioms EffectiveEncoding.AngleCode.Fits.mono
#check EffectiveEncoding.AngleCode.Fits.neg
set_option pp.universes false in #print axioms EffectiveEncoding.AngleCode.Fits.neg
#check EffectiveEncoding.AngleCode.Fits.half
set_option pp.universes false in #print axioms EffectiveEncoding.AngleCode.Fits.half
#check EffectiveEncoding.SingleCode.Fits.mono
set_option pp.universes false in #print axioms EffectiveEncoding.SingleCode.Fits.mono
#check EffectiveEncoding.GateCode.Fits.mono
set_option pp.universes false in #print axioms EffectiveEncoding.GateCode.Fits.mono
#check EffectiveEncoding.WordFits.mono
set_option pp.universes false in #print axioms EffectiveEncoding.WordFits.mono
#check EffectiveEncoding.wordFits_nil
set_option pp.universes false in #print axioms EffectiveEncoding.wordFits_nil
#check EffectiveEncoding.wordFits_append
set_option pp.universes false in #print axioms EffectiveEncoding.wordFits_append
#check EffectiveEncoding.WordFits.reverse
set_option pp.universes false in #print axioms EffectiveEncoding.WordFits.reverse
#check EffectiveEncoding.cnotCode_fits
set_option pp.universes false in #print axioms EffectiveEncoding.cnotCode_fits
#check EffectiveEncoding.parityCode_fits
set_option pp.universes false in #print axioms EffectiveEncoding.parityCode_fits
#check EffectiveEncoding.pauliCode_fits
set_option pp.universes false in #print axioms EffectiveEncoding.pauliCode_fits
#check EffectiveEncoding.signedCode_fits
set_option pp.universes false in #print axioms EffectiveEncoding.signedCode_fits
#check EffectiveEncoding.selectedCode_fits
set_option pp.universes false in #print axioms EffectiveEncoding.selectedCode_fits
#check EffectiveEncoding.piCode_fits
set_option pp.universes false in #print axioms EffectiveEncoding.piCode_fits
#check EffectiveEncoding.hadamardCode_fits
set_option pp.universes false in #print axioms EffectiveEncoding.hadamardCode_fits
#check EffectiveEncoding.adjacentSwapCode_fits
set_option pp.universes false in #print axioms EffectiveEncoding.adjacentSwapCode_fits
#check EffectiveEncoding.adjacentRotationCode_fits
set_option pp.universes false in #print axioms EffectiveEncoding.adjacentRotationCode_fits
#check EffectiveEncoding.orientedRotationCode_fits
set_option pp.universes false in #print axioms EffectiveEncoding.orientedRotationCode_fits
#check EffectiveEncoding.moveCode_fits
set_option pp.universes false in #print axioms EffectiveEncoding.moveCode_fits
#check EffectiveEncoding.swapCode_fits
set_option pp.universes false in #print axioms EffectiveEncoding.swapCode_fits
#check EffectiveEncoding.rotationCode_fits
set_option pp.universes false in #print axioms EffectiveEncoding.rotationCode_fits
#check EffectiveEncoding.RawCode.compile_fits
set_option pp.universes false in #print axioms EffectiveEncoding.RawCode.compile_fits
#check EffectiveEncoding.compileRaw_fits
set_option pp.universes false in #print axioms EffectiveEncoding.compileRaw_fits
#check EffectiveEncoding.alignmentCode_fits
set_option pp.universes false in #print axioms EffectiveEncoding.alignmentCode_fits
#check EffectiveEncoding.countProgram_fits
set_option pp.universes false in #print axioms EffectiveEncoding.countProgram_fits
#check EffectiveEncoding.branchCode_fits
set_option pp.universes false in #print axioms EffectiveEncoding.branchCode_fits
#check EffectiveEncoding.occupationStepCode_fits
set_option pp.universes false in #print axioms EffectiveEncoding.occupationStepCode_fits
#check EffectiveEncoding.halvingBudget_mono
set_option pp.universes false in #print axioms EffectiveEncoding.halvingBudget_mono
#check EffectiveEncoding.stageCode_fits
set_option pp.universes false in #print axioms EffectiveEncoding.stageCode_fits
#check EffectiveEncoding.WordFits.shift
set_option pp.universes false in #print axioms EffectiveEncoding.WordFits.shift
#check EffectiveEncoding.WordFits.prefix
set_option pp.universes false in #print axioms EffectiveEncoding.WordFits.prefix
#check EffectiveEncoding.WordFits.cast
set_option pp.universes false in #print axioms EffectiveEncoding.WordFits.cast
#check EffectiveEncoding.compressionCode_fits
set_option pp.universes false in #print axioms EffectiveEncoding.compressionCode_fits
#check EffectiveEncoding.bellPairsCode_fits
set_option pp.universes false in #print axioms EffectiveEncoding.bellPairsCode_fits
#check EffectiveEncoding.extractionCode_fits
set_option pp.universes false in #print axioms EffectiveEncoding.extractionCode_fits
#check EffectiveEncoding.binaryWidth_mono
set_option pp.universes false in #print axioms EffectiveEncoding.binaryWidth_mono
#check EffectiveEncoding.AngleCode.descriptionWeight_bound
set_option pp.universes false in #print axioms EffectiveEncoding.AngleCode.descriptionWeight_bound
#check EffectiveEncoding.SingleCode.descriptionWeight_bound
set_option pp.universes false in #print axioms EffectiveEncoding.SingleCode.descriptionWeight_bound
#check EffectiveEncoding.GateCode.descriptionWeight_bound
set_option pp.universes false in #print axioms EffectiveEncoding.GateCode.descriptionWeight_bound
#check EffectiveEncoding.codeDescriptionWeight_bound
set_option pp.universes false in #print axioms EffectiveEncoding.codeDescriptionWeight_bound
#check EffectiveEncoding.extractionCode_descriptionWeight
set_option pp.universes false in #print axioms EffectiveEncoding.extractionCode_descriptionWeight
#check EffectiveEncoding.AngleCode.neg_value
set_option pp.universes false in #print axioms EffectiveEncoding.AngleCode.neg_value
#check EffectiveEncoding.AngleCode.half_value
set_option pp.universes false in #print axioms EffectiveEncoding.AngleCode.half_value
#check EffectiveEncoding.piCode_value
set_option pp.universes false in #print axioms EffectiveEncoding.piCode_value
#check EffectiveEncoding.GateCode.inverse_value
set_option pp.universes false in #print axioms EffectiveEncoding.GateCode.inverse_value
#check EffectiveEncoding.interpret_length
set_option pp.universes false in #print axioms EffectiveEncoding.interpret_length
#check EffectiveEncoding.interpret_append
set_option pp.universes false in #print axioms EffectiveEncoding.interpret_append
#check EffectiveEncoding.interpret_reverse
set_option pp.universes false in #print axioms EffectiveEncoding.interpret_reverse
#check EffectiveEncoding.reverseCode_length
set_option pp.universes false in #print axioms EffectiveEncoding.reverseCode_length
#check EffectiveEncoding.maskOfBits_injective
set_option pp.universes false in #print axioms EffectiveEncoding.maskOfBits_injective
#check EffectiveEncoding.maskIndex_injective
set_option pp.universes false in #print axioms EffectiveEncoding.maskIndex_injective
#check EffectiveEncoding.masks_nodup
set_option pp.universes false in #print axioms EffectiveEncoding.masks_nodup
#check EffectiveEncoding.mem_masks
set_option pp.universes false in #print axioms EffectiveEncoding.mem_masks
#check EffectiveEncoding.masks_length
set_option pp.universes false in #print axioms EffectiveEncoding.masks_length
#check EffectiveEncoding.masks_perm
set_option pp.universes false in #print axioms EffectiveEncoding.masks_perm
#check EffectiveEncoding.controls_length
set_option pp.universes false in #print axioms EffectiveEncoding.controls_length
#check EffectiveEncoding.controls_character
set_option pp.universes false in #print axioms EffectiveEncoding.controls_character
#check EffectiveEncoding.interpret_cnotCode
set_option pp.universes false in #print axioms EffectiveEncoding.interpret_cnotCode
#check EffectiveEncoding.parityCode_action
set_option pp.universes false in #print axioms EffectiveEncoding.parityCode_action
#check EffectiveEncoding.parityCode_length
set_option pp.universes false in #print axioms EffectiveEncoding.parityCode_length
#check EffectiveEncoding.pauliCode_action
set_option pp.universes false in #print axioms EffectiveEncoding.pauliCode_action
#check EffectiveEncoding.pauliCode_length
set_option pp.universes false in #print axioms EffectiveEncoding.pauliCode_length
#check EffectiveEncoding.signedCode_value
set_option pp.universes false in #print axioms EffectiveEncoding.signedCode_value
#check EffectiveEncoding.maskParity_sign
set_option pp.universes false in #print axioms EffectiveEncoding.maskParity_sign
#check EffectiveEncoding.run_pauliCodes
set_option pp.universes false in #print axioms EffectiveEncoding.run_pauliCodes
#check EffectiveEncoding.selectedCode_action
set_option pp.universes false in #print axioms EffectiveEncoding.selectedCode_action
#check EffectiveEncoding.selectedCode_length
set_option pp.universes false in #print axioms EffectiveEncoding.selectedCode_length
#check EffectiveEncoding.mem_triples
set_option pp.universes false in #print axioms EffectiveEncoding.mem_triples
#check EffectiveEncoding.triples_nodup
set_option pp.universes false in #print axioms EffectiveEncoding.triples_nodup
#check EffectiveEncoding.fromTriple_count_zero
set_option pp.universes false in #print axioms EffectiveEncoding.fromTriple_count_zero
#check EffectiveEncoding.fromTriple_count_one
set_option pp.universes false in #print axioms EffectiveEncoding.fromTriple_count_one
#check EffectiveEncoding.fromTriple_count_two
set_option pp.universes false in #print axioms EffectiveEncoding.fromTriple_count_two
#check EffectiveEncoding.fromTriple_count_three
set_option pp.universes false in #print axioms EffectiveEncoding.fromTriple_count_three
#check EffectiveEncoding.count_total
set_option pp.universes false in #print axioms EffectiveEncoding.count_total
#check EffectiveEncoding.toTriple_le
set_option pp.universes false in #print axioms EffectiveEncoding.toTriple_le
#check EffectiveEncoding.toTriple_fromTriple
set_option pp.universes false in #print axioms EffectiveEncoding.toTriple_fromTriple
#check EffectiveEncoding.fromTriple_toTriple
set_option pp.universes false in #print axioms EffectiveEncoding.fromTriple_toTriple
#check EffectiveEncoding.occupations_nodup
set_option pp.universes false in #print axioms EffectiveEncoding.occupations_nodup
#check EffectiveEncoding.mem_occupations
set_option pp.universes false in #print axioms EffectiveEncoding.mem_occupations
#check EffectiveEncoding.occupations_length
set_option pp.universes false in #print axioms EffectiveEncoding.occupations_length
#check EffectiveEncoding.unrank_rank
set_option pp.universes false in #print axioms EffectiveEncoding.unrank_rank
#check EffectiveEncoding.rank_unrank
set_option pp.universes false in #print axioms EffectiveEncoding.rank_unrank
#check EffectiveEncoding.boundedBits_injective
set_option pp.universes false in #print axioms EffectiveEncoding.boundedBits_injective
#check EffectiveEncoding.rank_fits
set_option pp.universes false in #print axioms EffectiveEncoding.rank_fits
#check EffectiveEncoding.find_unique
set_option pp.universes false in #print axioms EffectiveEncoding.find_unique
#check EffectiveEncoding.decode_encode
set_option pp.universes false in #print axioms EffectiveEncoding.decode_encode
#check EffectiveEncoding.decode_some_iff
set_option pp.universes false in #print axioms EffectiveEncoding.decode_some_iff
#check EffectiveEncoding.enumeration_candidate_bound
set_option pp.universes false in #print axioms EffectiveEncoding.enumeration_candidate_bound
#check EffectiveEncoding.compactEncoding_testBit
set_option pp.universes false in #print axioms EffectiveEncoding.compactEncoding_testBit
#check EffectiveEncoding.originalEncoding_high_zero
set_option pp.universes false in #print axioms EffectiveEncoding.originalEncoding_high_zero
#check EffectiveEncoding.interpret_cast
set_option pp.universes false in #print axioms EffectiveEncoding.interpret_cast
#check EffectiveEncoding.castCode_length
set_option pp.universes false in #print axioms EffectiveEncoding.castCode_length
#check EffectiveEncoding.interpret_bellPreparationCode
set_option pp.universes false in #print axioms EffectiveEncoding.interpret_bellPreparationCode
#check EffectiveEncoding.interpret_bellPairsCode
set_option pp.universes false in #print axioms EffectiveEncoding.interpret_bellPairsCode
#check EffectiveEncoding.extractionCircuit_eq
set_option pp.universes false in #print axioms EffectiveEncoding.extractionCircuit_eq
#check EffectiveEncoding.extractionCircuit_gate
set_option pp.universes false in #print axioms EffectiveEncoding.extractionCircuit_gate
#check EffectiveEncoding.extractionCircuit_coherent
set_option pp.universes false in #print axioms EffectiveEncoding.extractionCircuit_coherent
#check EffectiveEncoding.extractionCircuit_purePower
set_option pp.universes false in #print axioms EffectiveEncoding.extractionCircuit_purePower
#check EffectiveEncoding.extractionCode_length
set_option pp.universes false in #print axioms EffectiveEncoding.extractionCode_length
#check EffectiveEncoding.extractionCode_polynomial_bound
set_option pp.universes false in #print axioms EffectiveEncoding.extractionCode_polynomial_bound
#check EffectiveEncoding.extractionCircuit_polynomial_bound
set_option pp.universes false in #print axioms EffectiveEncoding.extractionCircuit_polynomial_bound
#check EffectiveEncoding.extractionVector_readout
set_option pp.universes false in #print axioms EffectiveEncoding.extractionVector_readout
#check EffectiveEncoding.garbageVector_square
set_option pp.universes false in #print axioms EffectiveEncoding.garbageVector_square
#check EffectiveEncoding.extractionOutput_coherent
set_option pp.universes false in #print axioms EffectiveEncoding.extractionOutput_coherent
#check EffectiveEncoding.extractionOutput_purePower
set_option pp.universes false in #print axioms EffectiveEncoding.extractionOutput_purePower
#check EffectiveEncoding.wireLabels_value
set_option pp.universes false in #print axioms EffectiveEncoding.wireLabels_value
#check EffectiveEncoding.labelCircuit_flatMap
set_option pp.universes false in #print axioms EffectiveEncoding.labelCircuit_flatMap
#check EffectiveEncoding.labelCircuit_uses
set_option pp.universes false in #print axioms EffectiveEncoding.labelCircuit_uses
#check EffectiveEncoding.compileLabels_error
set_option pp.universes false in #print axioms EffectiveEncoding.compileLabels_error
#check EffectiveEncoding.compileLabelWord_error
set_option pp.universes false in #print axioms EffectiveEncoding.compileLabelWord_error
#check EffectiveEncoding.compileLabels_length
set_option pp.universes false in #print axioms EffectiveEncoding.compileLabels_length
#check EffectiveEncoding.compileLabelWord_length
set_option pp.universes false in #print axioms EffectiveEncoding.compileLabelWord_length
#check EffectiveEncoding.extractionOutput_fidelity_one
set_option pp.universes false in #print axioms EffectiveEncoding.extractionOutput_fidelity_one
#check EffectiveEncoding.extractionOutput_robust
set_option pp.universes false in #print axioms EffectiveEncoding.extractionOutput_robust
#check EffectiveEncoding.extractionOutput_robust_up_to_phase
set_option pp.universes false in #print axioms EffectiveEncoding.extractionOutput_robust_up_to_phase
#check EffectiveEncoding.finiteLabels_fidelity
set_option pp.universes false in #print axioms EffectiveEncoding.finiteLabels_fidelity
#check EffectiveEncoding.selectedCode_run_eq
set_option pp.universes false in #print axioms EffectiveEncoding.selectedCode_run_eq
#check EffectiveEncoding.adjacentSwapCode_run_eq
set_option pp.universes false in #print axioms EffectiveEncoding.adjacentSwapCode_run_eq
#check EffectiveEncoding.adjacentSwapCode_length
set_option pp.universes false in #print axioms EffectiveEncoding.adjacentSwapCode_length
#check EffectiveEncoding.adjacentRotationCode_run_eq
set_option pp.universes false in #print axioms EffectiveEncoding.adjacentRotationCode_run_eq
#check EffectiveEncoding.adjacentRotationCode_length
set_option pp.universes false in #print axioms EffectiveEncoding.adjacentRotationCode_length
#check EffectiveEncoding.orientedRotationCode_run_eq
set_option pp.universes false in #print axioms EffectiveEncoding.orientedRotationCode_run_eq
#check EffectiveEncoding.mem_otherWires
set_option pp.universes false in #print axioms EffectiveEncoding.mem_otherWires
#check EffectiveEncoding.otherWires_length
set_option pp.universes false in #print axioms EffectiveEncoding.otherWires_length
#check EffectiveEncoding.differing_exists
set_option pp.universes false in #print axioms EffectiveEncoding.differing_exists
#check EffectiveEncoding.differingWire_spec
set_option pp.universes false in #print axioms EffectiveEncoding.differingWire_spec
#check EffectiveEncoding.clearBits_otherWires
set_option pp.universes false in #print axioms EffectiveEncoding.clearBits_otherWires
#check EffectiveEncoding.moveCode_run_eq
set_option pp.universes false in #print axioms EffectiveEncoding.moveCode_run_eq
#check EffectiveEncoding.moveCode_length
set_option pp.universes false in #print axioms EffectiveEncoding.moveCode_length
#check EffectiveEncoding.swapCode_action
set_option pp.universes false in #print axioms EffectiveEncoding.swapCode_action
#check EffectiveEncoding.swapCode_length
set_option pp.universes false in #print axioms EffectiveEncoding.swapCode_length
#check EffectiveEncoding.rotationCode_action
set_option pp.universes false in #print axioms EffectiveEncoding.rotationCode_action
#check EffectiveEncoding.rotationCode_length
set_option pp.universes false in #print axioms EffectiveEncoding.rotationCode_length
#check EffectiveEncoding.GateCode.globalPhase_norm
set_option pp.universes false in #print axioms EffectiveEncoding.GateCode.globalPhase_norm
#check EffectiveEncoding.GateCode.representative_spec
set_option pp.universes false in #print axioms EffectiveEncoding.GateCode.representative_spec
#check EffectiveEncoding.wordPhase_norm
set_option pp.universes false in #print axioms EffectiveEncoding.wordPhase_norm
#check EffectiveEncoding.interpret_cons
set_option pp.universes false in #print axioms EffectiveEncoding.interpret_cons
#check EffectiveEncoding.representativeCircuit_cons
set_option pp.universes false in #print axioms EffectiveEncoding.representativeCircuit_cons
#check EffectiveEncoding.representativeCircuit_phase
set_option pp.universes false in #print axioms EffectiveEncoding.representativeCircuit_phase
#check EffectiveEncoding.descriptor_word_error
set_option pp.universes false in #print axioms EffectiveEncoding.descriptor_word_error
#check EffectiveEncoding.descriptor_word_uniform_error
set_option pp.universes false in #print axioms EffectiveEncoding.descriptor_word_uniform_error
#check EffectiveEncoding.descriptorSynthesis_spec
set_option pp.universes false in #print axioms EffectiveEncoding.descriptorSynthesis_spec
#check EffectiveEncoding.numericalExtractionCode_uses
set_option pp.universes false in #print axioms EffectiveEncoding.numericalExtractionCode_uses
#check EffectiveEncoding.numericalExtractionCode_error
set_option pp.universes false in #print axioms EffectiveEncoding.numericalExtractionCode_error
#check EffectiveEncoding.numericalExtractionCode_length
set_option pp.universes false in #print axioms EffectiveEncoding.numericalExtractionCode_length
#check EffectiveEncoding.numericalExtractionCode_fidelity
set_option pp.universes false in #print axioms EffectiveEncoding.numericalExtractionCode_fidelity
#check EffectiveEncoding.descriptorArithmeticOperations_bound
set_option pp.universes false in #print axioms EffectiveEncoding.descriptorArithmeticOperations_bound
#check EffectiveEncoding.extractionArithmeticOperations_bound
set_option pp.universes false in #print axioms EffectiveEncoding.extractionArithmeticOperations_bound
#check EffectiveEncoding.numericalExtraction_from_universal
set_option pp.universes false in #print axioms EffectiveEncoding.numericalExtraction_from_universal
#check EffectiveEncoding.countProgram_length
set_option pp.universes false in #print axioms EffectiveEncoding.countProgram_length
#check EffectiveEncoding.countProgram_sparse
set_option pp.universes false in #print axioms EffectiveEncoding.countProgram_sparse
#check EffectiveEncoding.indexedCount_image
set_option pp.universes false in #print axioms EffectiveEncoding.indexedCount_image
#check EffectiveEncoding.indexedCount_ratio
set_option pp.universes false in #print axioms EffectiveEncoding.indexedCount_ratio
#check EffectiveEncoding.explicitOthers_perm
set_option pp.universes false in #print axioms EffectiveEncoding.explicitOthers_perm
#check EffectiveEncoding.explicitOthers_nodup
set_option pp.universes false in #print axioms EffectiveEncoding.explicitOthers_nodup
#check EffectiveEncoding.explicitOthers_length
set_option pp.universes false in #print axioms EffectiveEncoding.explicitOthers_length
#check EffectiveEncoding.integerIndexedCode_raw
set_option pp.universes false in #print axioms EffectiveEncoding.integerIndexedCode_raw
#check EffectiveEncoding.integerIndexedCode_action
set_option pp.universes false in #print axioms EffectiveEncoding.integerIndexedCode_action
#check EffectiveEncoding.integerIndexedCode_fixes_zero
set_option pp.universes false in #print axioms EffectiveEncoding.integerIndexedCode_fixes_zero
#check EffectiveEncoding.integerIndexedCode_length
set_option pp.universes false in #print axioms EffectiveEncoding.integerIndexedCode_length
#check EffectiveEncoding.branchEmbedding_eq
set_option pp.universes false in #print axioms EffectiveEncoding.branchEmbedding_eq
#check EffectiveEncoding.branchCode_action
set_option pp.universes false in #print axioms EffectiveEncoding.branchCode_action
#check EffectiveEncoding.branchCode_fixes_other
set_option pp.universes false in #print axioms EffectiveEncoding.branchCode_fixes_other
#check EffectiveEncoding.branchCode_fixes_other_pivot
set_option pp.universes false in #print axioms EffectiveEncoding.branchCode_fixes_other_pivot
#check EffectiveEncoding.branchCode_length
set_option pp.universes false in #print axioms EffectiveEncoding.branchCode_length
#check EffectiveEncoding.swapCode_denote
set_option pp.universes false in #print axioms EffectiveEncoding.swapCode_denote
#check EffectiveEncoding.rotationCode_denote_eq
set_option pp.universes false in #print axioms EffectiveEncoding.rotationCode_denote_eq
#check EffectiveEncoding.mergeCode_value
set_option pp.universes false in #print axioms EffectiveEncoding.mergeCode_value
#check EffectiveEncoding.RawCode.compile_denote
set_option pp.universes false in #print axioms EffectiveEncoding.RawCode.compile_denote
#check EffectiveEncoding.RawCode.compile_length
set_option pp.universes false in #print axioms EffectiveEncoding.RawCode.compile_length
#check EffectiveEncoding.compileRaw_denote
set_option pp.universes false in #print axioms EffectiveEncoding.compileRaw_denote
#check EffectiveEncoding.compileRaw_length
set_option pp.universes false in #print axioms EffectiveEncoding.compileRaw_length
#check EffectiveEncoding.alignmentPerm_complete
set_option pp.universes false in #print axioms EffectiveEncoding.alignmentPerm_complete
#check EffectiveEncoding.alignmentCode_action
set_option pp.universes false in #print axioms EffectiveEncoding.alignmentCode_action
#check EffectiveEncoding.alignmentCode_length
set_option pp.universes false in #print axioms EffectiveEncoding.alignmentCode_length
#check EffectiveEncoding.alignmentCode_on_embedding
set_option pp.universes false in #print axioms EffectiveEncoding.alignmentCode_on_embedding
#check EffectiveEncoding.star_complexPhase
set_option pp.universes false in #print axioms EffectiveEncoding.star_complexPhase
#check EffectiveEncoding.phaseRepresentative_bool
set_option pp.universes false in #print axioms EffectiveEncoding.phaseRepresentative_bool
#check EffectiveEncoding.su2ToBool_star
set_option pp.universes false in #print axioms EffectiveEncoding.su2ToBool_star
#check EffectiveEncoding.SingleCode.globalPhase_norm
set_option pp.universes false in #print axioms EffectiveEncoding.SingleCode.globalPhase_norm
#check EffectiveEncoding.SingleCode.representative_spec
set_option pp.universes false in #print axioms EffectiveEncoding.SingleCode.representative_spec
#check EffectiveEncoding.quaternionCoordinates_star
set_option pp.universes false in #print axioms EffectiveEncoding.quaternionCoordinates_star
#check EffectiveEncoding.sqrt_half_eq_invSqrtTwo
set_option pp.universes false in #print axioms EffectiveEncoding.sqrt_half_eq_invSqrtTwo
#check EffectiveEncoding.invSqrtTwoOracle_correct
set_option pp.universes false in #print axioms EffectiveEncoding.invSqrtTwoOracle_correct
#check EffectiveEncoding.phaseCosOracle_correct
set_option pp.universes false in #print axioms EffectiveEncoding.phaseCosOracle_correct
#check EffectiveEncoding.phaseSinOracle_correct
set_option pp.universes false in #print axioms EffectiveEncoding.phaseSinOracle_correct
#check EffectiveEncoding.quaternionStarOracle_correct
set_option pp.universes false in #print axioms EffectiveEncoding.quaternionStarOracle_correct
#check EffectiveEncoding.coordinatePacket_correct
set_option pp.universes false in #print axioms EffectiveEncoding.coordinatePacket_correct
#check EffectiveEncoding.hadRepresentative_coordinates
set_option pp.universes false in #print axioms EffectiveEncoding.hadRepresentative_coordinates
#check EffectiveEncoding.phaseRepresentative_coordinates
set_option pp.universes false in #print axioms EffectiveEncoding.phaseRepresentative_coordinates
#check EffectiveEncoding.SingleCode.quaternionOracle_correct
set_option pp.universes false in #print axioms EffectiveEncoding.SingleCode.quaternionOracle_correct
#check CircuitRecursion.ScalarExpression
set_option pp.universes false in #print axioms CircuitRecursion.ScalarExpression
#check CircuitRecursion.PacketExpression
set_option pp.universes false in #print axioms CircuitRecursion.PacketExpression
#check CircuitRecursion.ScalarExpression.eval
set_option pp.universes false in #print axioms CircuitRecursion.ScalarExpression.eval
#check CircuitRecursion.PacketExpression.eval
set_option pp.universes false in #print axioms CircuitRecursion.PacketExpression.eval
#check CircuitRecursion.ScalarExpression.operations
set_option pp.universes false in #print axioms CircuitRecursion.ScalarExpression.operations
#check CircuitRecursion.PacketExpression.operations
set_option pp.universes false in #print axioms CircuitRecursion.PacketExpression.operations
#check CircuitRecursion.ScalarExpressionOracle
set_option pp.universes false in #print axioms CircuitRecursion.ScalarExpressionOracle
#check CircuitRecursion.PacketExpressionOracle
set_option pp.universes false in #print axioms CircuitRecursion.PacketExpressionOracle
#check CircuitRecursion.evaluateScalarOracle
set_option pp.universes false in #print axioms CircuitRecursion.evaluateScalarOracle
#check CircuitRecursion.evaluatePacketOracle
set_option pp.universes false in #print axioms CircuitRecursion.evaluatePacketOracle
#check CircuitRecursion.expressionAdd
set_option pp.universes false in #print axioms CircuitRecursion.expressionAdd
#check CircuitRecursion.expressionNeg
set_option pp.universes false in #print axioms CircuitRecursion.expressionNeg
#check CircuitRecursion.expressionMul
set_option pp.universes false in #print axioms CircuitRecursion.expressionMul
#check CircuitRecursion.expressionInv
set_option pp.universes false in #print axioms CircuitRecursion.expressionInv
#check CircuitRecursion.expressionSqrt
set_option pp.universes false in #print axioms CircuitRecursion.expressionSqrt
#check CircuitRecursion.expressionMeanMinus
set_option pp.universes false in #print axioms CircuitRecursion.expressionMeanMinus
#check CircuitRecursion.expressionCoordinate
set_option pp.universes false in #print axioms CircuitRecursion.expressionCoordinate
#check CircuitRecursion.expressionPacketMul
set_option pp.universes false in #print axioms CircuitRecursion.expressionPacketMul
#check CircuitRecursion.expressionPacketInverse
set_option pp.universes false in #print axioms CircuitRecursion.expressionPacketInverse
#check CircuitRecursion.expressionPacketOne
set_option pp.universes false in #print axioms CircuitRecursion.expressionPacketOne
#check CircuitRecursion.expressionFrame
set_option pp.universes false in #print axioms CircuitRecursion.expressionFrame
#check CircuitRecursion.expressionDistance
set_option pp.universes false in #print axioms CircuitRecursion.expressionDistance
#check CircuitRecursion.balancedS
set_option pp.universes false in #print axioms CircuitRecursion.balancedS
#check CircuitRecursion.balancedC
set_option pp.universes false in #print axioms CircuitRecursion.balancedC
#check CircuitRecursion.referenceX
set_option pp.universes false in #print axioms CircuitRecursion.referenceX
#check CircuitRecursion.referenceY
set_option pp.universes false in #print axioms CircuitRecursion.referenceY
#check CircuitRecursion.balancedReference
set_option pp.universes false in #print axioms CircuitRecursion.balancedReference
#check CircuitRecursion.coordinateOracle
set_option pp.universes false in #print axioms CircuitRecursion.coordinateOracle
#check CircuitRecursion.balancedSOracle
set_option pp.universes false in #print axioms CircuitRecursion.balancedSOracle
#check CircuitRecursion.balancedCOracle
set_option pp.universes false in #print axioms CircuitRecursion.balancedCOracle
#check CircuitRecursion.referenceXOracle
set_option pp.universes false in #print axioms CircuitRecursion.referenceXOracle
#check CircuitRecursion.referenceYOracle
set_option pp.universes false in #print axioms CircuitRecursion.referenceYOracle
#check CircuitRecursion.balancedReferenceOracle
set_option pp.universes false in #print axioms CircuitRecursion.balancedReferenceOracle
#check CircuitRecursion.cachePrecisionBudget
set_option pp.universes false in #print axioms CircuitRecursion.cachePrecisionBudget
#check CircuitRecursion.dyadicPacketBits
set_option pp.universes false in #print axioms CircuitRecursion.dyadicPacketBits
#check CircuitRecursion.cachedInputBits
set_option pp.universes false in #print axioms CircuitRecursion.cachedInputBits
#check CircuitRecursion.cachedArithmeticRun
set_option pp.universes false in #print axioms CircuitRecursion.cachedArithmeticRun
#check CircuitRecursion.buildPacketCache
set_option pp.universes false in #print axioms CircuitRecursion.buildPacketCache
#check CircuitRecursion.readPacketCache
set_option pp.universes false in #print axioms CircuitRecursion.readPacketCache
#check CircuitRecursion.CachedWordResult
set_option pp.universes false in #print axioms CircuitRecursion.CachedWordResult
#check CircuitRecursion.cachedNumericalRun
set_option pp.universes false in #print axioms CircuitRecursion.cachedNumericalRun
#check CircuitRecursion.quaternionConjugateOracle
set_option pp.universes false in #print axioms CircuitRecursion.quaternionConjugateOracle
#check CircuitRecursion.conditionedConjugatorOracle
set_option pp.universes false in #print axioms CircuitRecursion.conditionedConjugatorOracle
#check CircuitRecursion.conditionedFactorXOracle
set_option pp.universes false in #print axioms CircuitRecursion.conditionedFactorXOracle
#check CircuitRecursion.conditionedFactorYOracle
set_option pp.universes false in #print axioms CircuitRecursion.conditionedFactorYOracle
#check CircuitRecursion.quaternionOracleInverse
set_option pp.universes false in #print axioms CircuitRecursion.quaternionOracleInverse
#check CircuitRecursion.frameOracle
set_option pp.universes false in #print axioms CircuitRecursion.frameOracle
#check CircuitRecursion.chartTargetOracle
set_option pp.universes false in #print axioms CircuitRecursion.chartTargetOracle
#check CircuitRecursion.chartMassScore
set_option pp.universes false in #print axioms CircuitRecursion.chartMassScore
#check CircuitRecursion.chooseChart
set_option pp.universes false in #print axioms CircuitRecursion.chooseChart
#check CircuitRecursion.residualSmall
set_option pp.universes false in #print axioms CircuitRecursion.residualSmall
#check CircuitRecursion.ScalarExpression.executedOperations
set_option pp.universes false in #print axioms CircuitRecursion.ScalarExpression.executedOperations
#check CircuitRecursion.PacketExpression.executedOperations
set_option pp.universes false in #print axioms CircuitRecursion.PacketExpression.executedOperations
#check CircuitRecursion.ArithmeticWordResult.executedOperations
set_option pp.universes false in #print axioms CircuitRecursion.ArithmeticWordResult.executedOperations
#check CircuitRecursion.expressionPowerTwo
set_option pp.universes false in #print axioms CircuitRecursion.expressionPowerTwo
#check CircuitRecursion.executeExpressionRoot
set_option pp.universes false in #print axioms CircuitRecursion.executeExpressionRoot
#check CircuitRecursion.executeStoppingThreshold
set_option pp.universes false in #print axioms CircuitRecursion.executeStoppingThreshold
#check CircuitRecursion.ScalarExpression.run
set_option pp.universes false in #print axioms CircuitRecursion.ScalarExpression.run
#check CircuitRecursion.PacketExpression.run
set_option pp.universes false in #print axioms CircuitRecursion.PacketExpression.run
#check CircuitRecursion.ScalarOperationBound
set_option pp.universes false in #print axioms CircuitRecursion.ScalarOperationBound
#check CircuitRecursion.PacketOperationBound
set_option pp.universes false in #print axioms CircuitRecursion.PacketOperationBound
#check CircuitRecursion.BitEnvelope
set_option pp.universes false in #print axioms CircuitRecursion.BitEnvelope
#check CircuitRecursion.ScalarBitEnvelope
set_option pp.universes false in #print axioms CircuitRecursion.ScalarBitEnvelope
#check CircuitRecursion.PacketBitEnvelope
set_option pp.universes false in #print axioms CircuitRecursion.PacketBitEnvelope
#check CircuitRecursion.bitAddEnvelope
set_option pp.universes false in #print axioms CircuitRecursion.bitAddEnvelope
#check CircuitRecursion.bitMulEnvelope
set_option pp.universes false in #print axioms CircuitRecursion.bitMulEnvelope
#check CircuitRecursion.bitInvEnvelope
set_option pp.universes false in #print axioms CircuitRecursion.bitInvEnvelope
#check CircuitRecursion.bitSqrtEnvelope
set_option pp.universes false in #print axioms CircuitRecursion.bitSqrtEnvelope
#check CircuitRecursion.bitMeanEnvelope
set_option pp.universes false in #print axioms CircuitRecursion.bitMeanEnvelope
#check CircuitRecursion.bitPacketMulEnvelope
set_option pp.universes false in #print axioms CircuitRecursion.bitPacketMulEnvelope
#check CircuitRecursion.bitDistanceEnvelope
set_option pp.universes false in #print axioms CircuitRecursion.bitDistanceEnvelope
#check CircuitRecursion.bitBalancedSEnvelope
set_option pp.universes false in #print axioms CircuitRecursion.bitBalancedSEnvelope
#check CircuitRecursion.bitBalancedCEnvelope
set_option pp.universes false in #print axioms CircuitRecursion.bitBalancedCEnvelope
#check CircuitRecursion.bitReferenceEnvelope
set_option pp.universes false in #print axioms CircuitRecursion.bitReferenceEnvelope
#check CircuitRecursion.bitBalancedReferenceEnvelope
set_option pp.universes false in #print axioms CircuitRecursion.bitBalancedReferenceEnvelope
#check CircuitRecursion.bitChartTargetEnvelope
set_option pp.universes false in #print axioms CircuitRecursion.bitChartTargetEnvelope
#check CircuitRecursion.bitChartMassEnvelope
set_option pp.universes false in #print axioms CircuitRecursion.bitChartMassEnvelope
#check CircuitRecursion.bitRadiusEnvelope
set_option pp.universes false in #print axioms CircuitRecursion.bitRadiusEnvelope
#check CircuitRecursion.bitNormalizedEnvelope
set_option pp.universes false in #print axioms CircuitRecursion.bitNormalizedEnvelope
#check CircuitRecursion.bitConjugatorEnvelope
set_option pp.universes false in #print axioms CircuitRecursion.bitConjugatorEnvelope
#check CircuitRecursion.bitFactorEnvelope
set_option pp.universes false in #print axioms CircuitRecursion.bitFactorEnvelope
#check CircuitRecursion.expressionBalancedS
set_option pp.universes false in #print axioms CircuitRecursion.expressionBalancedS
#check CircuitRecursion.expressionBalancedC
set_option pp.universes false in #print axioms CircuitRecursion.expressionBalancedC
#check CircuitRecursion.expressionReferenceX
set_option pp.universes false in #print axioms CircuitRecursion.expressionReferenceX
#check CircuitRecursion.expressionReferenceY
set_option pp.universes false in #print axioms CircuitRecursion.expressionReferenceY
#check CircuitRecursion.expressionBalancedReference
set_option pp.universes false in #print axioms CircuitRecursion.expressionBalancedReference
#check CircuitRecursion.expressionChartTarget
set_option pp.universes false in #print axioms CircuitRecursion.expressionChartTarget
#check CircuitRecursion.expressionChartMass
set_option pp.universes false in #print axioms CircuitRecursion.expressionChartMass
#check CircuitRecursion.expressionRadius
set_option pp.universes false in #print axioms CircuitRecursion.expressionRadius
#check CircuitRecursion.expressionNormalized
set_option pp.universes false in #print axioms CircuitRecursion.expressionNormalized
#check CircuitRecursion.expressionConjugator
set_option pp.universes false in #print axioms CircuitRecursion.expressionConjugator
#check CircuitRecursion.expressionConjugate
set_option pp.universes false in #print axioms CircuitRecursion.expressionConjugate
#check CircuitRecursion.expressionFactorX
set_option pp.universes false in #print axioms CircuitRecursion.expressionFactorX
#check CircuitRecursion.expressionFactorY
set_option pp.universes false in #print axioms CircuitRecursion.expressionFactorY
#check CircuitRecursion.cachedPacketExpression
set_option pp.universes false in #print axioms CircuitRecursion.cachedPacketExpression
#check CircuitRecursion.rationalBinaryExponent
set_option pp.universes false in #print axioms CircuitRecursion.rationalBinaryExponent
#check CircuitRecursion.ScalarExpression.integerBitBudget
set_option pp.universes false in #print axioms CircuitRecursion.ScalarExpression.integerBitBudget
#check CircuitRecursion.PacketExpression.integerBitBudget
set_option pp.universes false in #print axioms CircuitRecursion.PacketExpression.integerBitBudget
#check CircuitRecursion.IntegerScalar.meanMinus
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalar.meanMinus
#check CircuitRecursion.integerStoppingThreshold
set_option pp.universes false in #print axioms CircuitRecursion.integerStoppingThreshold
#check CircuitRecursion.ScalarExpression.integerRun
set_option pp.universes false in #print axioms CircuitRecursion.ScalarExpression.integerRun
#check CircuitRecursion.PacketExpression.integerRun
set_option pp.universes false in #print axioms CircuitRecursion.PacketExpression.integerRun
#check CircuitRecursion.IntegerPacket.inverse
set_option pp.universes false in #print axioms CircuitRecursion.IntegerPacket.inverse
#check CircuitRecursion.IntegerPacket.distanceNumerator
set_option pp.universes false in #print axioms CircuitRecursion.IntegerPacket.distanceNumerator
#check CircuitRecursion.IntegerPacket.distanceScalar
set_option pp.universes false in #print axioms CircuitRecursion.IntegerPacket.distanceScalar
#check CircuitRecursion.IntegerPacket
set_option pp.universes false in #print axioms CircuitRecursion.IntegerPacket
#check CircuitRecursion.IntegerPacket.value
set_option pp.universes false in #print axioms CircuitRecursion.IntegerPacket.value
#check CircuitRecursion.IntegerPacket.one
set_option pp.universes false in #print axioms CircuitRecursion.IntegerPacket.one
#check CircuitRecursion.IntegerPacket.mul
set_option pp.universes false in #print axioms CircuitRecursion.IntegerPacket.mul
#check CircuitRecursion.IntegerPacketHeight
set_option pp.universes false in #print axioms CircuitRecursion.IntegerPacketHeight
#check CircuitRecursion.IntegerPacketOracle
set_option pp.universes false in #print axioms CircuitRecursion.IntegerPacketOracle
#check CircuitRecursion.integerPacketOracle
set_option pp.universes false in #print axioms CircuitRecursion.integerPacketOracle
#check CircuitRecursion.integerPacketWord
set_option pp.universes false in #print axioms CircuitRecursion.integerPacketWord
#check CircuitRecursion.dyadicIntegerPacket
set_option pp.universes false in #print axioms CircuitRecursion.dyadicIntegerPacket
#check CircuitRecursion.cachedIntegerPacket
set_option pp.universes false in #print axioms CircuitRecursion.cachedIntegerPacket
#check CircuitRecursion.IntegerScalar
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalar
#check CircuitRecursion.IntegerScalar.value
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalar.value
#check CircuitRecursion.IntegerScalar.ofInt
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalar.ofInt
#check CircuitRecursion.IntegerScalar.add
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalar.add
#check CircuitRecursion.IntegerScalar.neg
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalar.neg
#check CircuitRecursion.IntegerScalar.mul
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalar.mul
#check CircuitRecursion.IntegerScalar.inv
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalar.inv
#check CircuitRecursion.IntegerScalarHeight
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalarHeight
#check CircuitRecursion.IntegerScalar.root
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalar.root
#check CircuitRecursion.IntegerScalar.ofRat
set_option pp.universes false in #print axioms CircuitRecursion.IntegerScalar.ofRat
#check CircuitRecursion.IntegerPacket.coordinate
set_option pp.universes false in #print axioms CircuitRecursion.IntegerPacket.coordinate
#check CircuitRecursion.IntegerPacket.ofScalars
set_option pp.universes false in #print axioms CircuitRecursion.IntegerPacket.ofScalars
#check CircuitRecursion.IntegerPacket.ofVector
set_option pp.universes false in #print axioms CircuitRecursion.IntegerPacket.ofVector
#check CircuitRecursion.normalizedQuaternionSU2
set_option pp.universes false in #print axioms CircuitRecursion.normalizedQuaternionSU2
#check CircuitRecursion.normalizedIntertwiner
set_option pp.universes false in #print axioms CircuitRecursion.normalizedIntertwiner
#check CircuitRecursion.coordinateSubOracle
set_option pp.universes false in #print axioms CircuitRecursion.coordinateSubOracle
#check CircuitRecursion.intertwinerRadiusOracle
set_option pp.universes false in #print axioms CircuitRecursion.intertwinerRadiusOracle
#check CircuitRecursion.normalizedIntertwinerOracle
set_option pp.universes false in #print axioms CircuitRecursion.normalizedIntertwinerOracle
#check CircuitRecursion.numericalCorrection
set_option pp.universes false in #print axioms CircuitRecursion.numericalCorrection
#check CircuitRecursion.correctionDemand
set_option pp.universes false in #print axioms CircuitRecursion.correctionDemand
#check CircuitRecursion.numericalDemand
set_option pp.universes false in #print axioms CircuitRecursion.numericalDemand
#check CircuitRecursion.correctionOperationSlope
set_option pp.universes false in #print axioms CircuitRecursion.correctionOperationSlope
#check CircuitRecursion.correctionOperationOffset
set_option pp.universes false in #print axioms CircuitRecursion.correctionOperationOffset
#check CircuitRecursion.WordOperationBound
set_option pp.universes false in #print axioms CircuitRecursion.WordOperationBound
#check CircuitRecursion.pairOperationSlope
set_option pp.universes false in #print axioms CircuitRecursion.pairOperationSlope
#check CircuitRecursion.pairOperationOffset
set_option pp.universes false in #print axioms CircuitRecursion.pairOperationOffset
#check CircuitRecursion.numericalThreshold
set_option pp.universes false in #print axioms CircuitRecursion.numericalThreshold
#check CircuitRecursion.numericalPairWord
set_option pp.universes false in #print axioms CircuitRecursion.numericalPairWord
#check CircuitRecursion.slopeGrowth
set_option pp.universes false in #print axioms CircuitRecursion.slopeGrowth
#check CircuitRecursion.offsetGrowth
set_option pp.universes false in #print axioms CircuitRecursion.offsetGrowth
#check CircuitRecursion.AgreesThrough
set_option pp.universes false in #print axioms CircuitRecursion.AgreesThrough
#check CircuitRecursion.expressionWord
set_option pp.universes false in #print axioms CircuitRecursion.expressionWord
#check CircuitRecursion.ArithmeticWordResult
set_option pp.universes false in #print axioms CircuitRecursion.ArithmeticWordResult
#check CircuitRecursion.ArithmeticWordResult.operations
set_option pp.universes false in #print axioms CircuitRecursion.ArithmeticWordResult.operations
#check CircuitRecursion.tracedBase
set_option pp.universes false in #print axioms CircuitRecursion.tracedBase
#check CircuitRecursion.tracedCorrection
set_option pp.universes false in #print axioms CircuitRecursion.tracedCorrection
#check CircuitRecursion.tracedPairWord
set_option pp.universes false in #print axioms CircuitRecursion.tracedPairWord
#check EffectiveEncoding.AngleAtom.cosOracle
set_option pp.universes false in #print axioms EffectiveEncoding.AngleAtom.cosOracle
#check EffectiveEncoding.AngleAtom.sinOracle
set_option pp.universes false in #print axioms EffectiveEncoding.AngleAtom.sinOracle
#check EffectiveEncoding.AngleCode.cosOracle
set_option pp.universes false in #print axioms EffectiveEncoding.AngleCode.cosOracle
#check EffectiveEncoding.AngleCode.sinOracle
set_option pp.universes false in #print axioms EffectiveEncoding.AngleCode.sinOracle
#check EffectiveEncoding.allBranchCode
set_option pp.universes false in #print axioms EffectiveEncoding.allBranchCode
#check EffectiveEncoding.occupationStepCode
set_option pp.universes false in #print axioms EffectiveEncoding.occupationStepCode
#check EffectiveEncoding.GateCode.extend
set_option pp.universes false in #print axioms EffectiveEncoding.GateCode.extend
#check EffectiveEncoding.prefixCode
set_option pp.universes false in #print axioms EffectiveEncoding.prefixCode
#check EffectiveEncoding.GateCode.shift
set_option pp.universes false in #print axioms EffectiveEncoding.GateCode.shift
#check EffectiveEncoding.shiftCode
set_option pp.universes false in #print axioms EffectiveEncoding.shiftCode
#check EffectiveEncoding.stageCode
set_option pp.universes false in #print axioms EffectiveEncoding.stageCode
#check EffectiveEncoding.stageCircuit
set_option pp.universes false in #print axioms EffectiveEncoding.stageCircuit
#check EffectiveEncoding.compressionCode
set_option pp.universes false in #print axioms EffectiveEncoding.compressionCode
#check EffectiveEncoding.compressionCircuit
set_option pp.universes false in #print axioms EffectiveEncoding.compressionCircuit
#check EffectiveEncoding.AngleCode.Fits
set_option pp.universes false in #print axioms EffectiveEncoding.AngleCode.Fits
#check EffectiveEncoding.SingleCode.Fits
set_option pp.universes false in #print axioms EffectiveEncoding.SingleCode.Fits
#check EffectiveEncoding.SingleCode.inverseDepth
set_option pp.universes false in #print axioms EffectiveEncoding.SingleCode.inverseDepth
#check EffectiveEncoding.GateCode.Fits
set_option pp.universes false in #print axioms EffectiveEncoding.GateCode.Fits
#check EffectiveEncoding.WordFits
set_option pp.universes false in #print axioms EffectiveEncoding.WordFits
#check EffectiveEncoding.RawCode.Fits
set_option pp.universes false in #print axioms EffectiveEncoding.RawCode.Fits
#check EffectiveEncoding.halvingBudget
set_option pp.universes false in #print axioms EffectiveEncoding.halvingBudget
#check EffectiveEncoding.binaryWidth
set_option pp.universes false in #print axioms EffectiveEncoding.binaryWidth
#check EffectiveEncoding.AngleCode.descriptionWeight
set_option pp.universes false in #print axioms EffectiveEncoding.AngleCode.descriptionWeight
#check EffectiveEncoding.angleWeightBudget
set_option pp.universes false in #print axioms EffectiveEncoding.angleWeightBudget
#check EffectiveEncoding.SingleCode.descriptionWeight
set_option pp.universes false in #print axioms EffectiveEncoding.SingleCode.descriptionWeight
#check EffectiveEncoding.GateCode.descriptionWeight
set_option pp.universes false in #print axioms EffectiveEncoding.GateCode.descriptionWeight
#check EffectiveEncoding.codeDescriptionWeight
set_option pp.universes false in #print axioms EffectiveEncoding.codeDescriptionWeight
#check EffectiveEncoding.AngleAtom
set_option pp.universes false in #print axioms EffectiveEncoding.AngleAtom
#check EffectiveEncoding.AngleCode
set_option pp.universes false in #print axioms EffectiveEncoding.AngleCode
#check EffectiveEncoding.AngleAtom.value
set_option pp.universes false in #print axioms EffectiveEncoding.AngleAtom.value
#check EffectiveEncoding.AngleCode.value
set_option pp.universes false in #print axioms EffectiveEncoding.AngleCode.value
#check EffectiveEncoding.AngleCode.neg
set_option pp.universes false in #print axioms EffectiveEncoding.AngleCode.neg
#check EffectiveEncoding.AngleCode.half
set_option pp.universes false in #print axioms EffectiveEncoding.AngleCode.half
#check EffectiveEncoding.piCode
set_option pp.universes false in #print axioms EffectiveEncoding.piCode
#check EffectiveEncoding.SingleCode
set_option pp.universes false in #print axioms EffectiveEncoding.SingleCode
#check EffectiveEncoding.SingleCode.value
set_option pp.universes false in #print axioms EffectiveEncoding.SingleCode.value
#check EffectiveEncoding.GateCode
set_option pp.universes false in #print axioms EffectiveEncoding.GateCode
#check EffectiveEncoding.GateCode.value
set_option pp.universes false in #print axioms EffectiveEncoding.GateCode.value
#check EffectiveEncoding.GateCode.inverse
set_option pp.universes false in #print axioms EffectiveEncoding.GateCode.inverse
#check EffectiveEncoding.WordCode
set_option pp.universes false in #print axioms EffectiveEncoding.WordCode
#check EffectiveEncoding.interpret
set_option pp.universes false in #print axioms EffectiveEncoding.interpret
#check EffectiveEncoding.reverseCode
set_option pp.universes false in #print axioms EffectiveEncoding.reverseCode
#check EffectiveEncoding.maskOfBits
set_option pp.universes false in #print axioms EffectiveEncoding.maskOfBits
#check EffectiveEncoding.masks
set_option pp.universes false in #print axioms EffectiveEncoding.masks
#check EffectiveEncoding.controls
set_option pp.universes false in #print axioms EffectiveEncoding.controls
#check EffectiveEncoding.cnotCode
set_option pp.universes false in #print axioms EffectiveEncoding.cnotCode
#check EffectiveEncoding.parityCode
set_option pp.universes false in #print axioms EffectiveEncoding.parityCode
#check EffectiveEncoding.pauliCode
set_option pp.universes false in #print axioms EffectiveEncoding.pauliCode
#check EffectiveEncoding.signedCode
set_option pp.universes false in #print axioms EffectiveEncoding.signedCode
#check EffectiveEncoding.maskParity
set_option pp.universes false in #print axioms EffectiveEncoding.maskParity
#check EffectiveEncoding.selectedCode
set_option pp.universes false in #print axioms EffectiveEncoding.selectedCode
#check EffectiveEncoding.Triple
set_option pp.universes false in #print axioms EffectiveEncoding.Triple
#check EffectiveEncoding.total
set_option pp.universes false in #print axioms EffectiveEncoding.total
#check EffectiveEncoding.triples
set_option pp.universes false in #print axioms EffectiveEncoding.triples
#check EffectiveEncoding.fromTriple
set_option pp.universes false in #print axioms EffectiveEncoding.fromTriple
#check EffectiveEncoding.toTriple
set_option pp.universes false in #print axioms EffectiveEncoding.toTriple
#check EffectiveEncoding.occupations
set_option pp.universes false in #print axioms EffectiveEncoding.occupations
#check EffectiveEncoding.rank
set_option pp.universes false in #print axioms EffectiveEncoding.rank
#check EffectiveEncoding.unrank
set_option pp.universes false in #print axioms EffectiveEncoding.unrank
#check EffectiveEncoding.rankEquiv
set_option pp.universes false in #print axioms EffectiveEncoding.rankEquiv
#check EffectiveEncoding.boundedBits
set_option pp.universes false in #print axioms EffectiveEncoding.boundedBits
#check EffectiveEncoding.compactEncoding
set_option pp.universes false in #print axioms EffectiveEncoding.compactEncoding
#check EffectiveEncoding.originalEncoding
set_option pp.universes false in #print axioms EffectiveEncoding.originalEncoding
#check EffectiveEncoding.nextEncoding
set_option pp.universes false in #print axioms EffectiveEncoding.nextEncoding
#check EffectiveEncoding.decode
set_option pp.universes false in #print axioms EffectiveEncoding.decode
#check EffectiveEncoding.castCode
set_option pp.universes false in #print axioms EffectiveEncoding.castCode
#check EffectiveEncoding.bellPreparationCode
set_option pp.universes false in #print axioms EffectiveEncoding.bellPreparationCode
#check EffectiveEncoding.bellPairsCode
set_option pp.universes false in #print axioms EffectiveEncoding.bellPairsCode
#check EffectiveEncoding.extractionCode
set_option pp.universes false in #print axioms EffectiveEncoding.extractionCode
#check EffectiveEncoding.extractionCircuit
set_option pp.universes false in #print axioms EffectiveEncoding.extractionCircuit
#check EffectiveEncoding.extractionVector
set_option pp.universes false in #print axioms EffectiveEncoding.extractionVector
#check EffectiveEncoding.garbageVector
set_option pp.universes false in #print axioms EffectiveEncoding.garbageVector
#check EffectiveEncoding.extractionOutput
set_option pp.universes false in #print axioms EffectiveEncoding.extractionOutput
#check EffectiveEncoding.LabelGate
set_option pp.universes false in #print axioms EffectiveEncoding.LabelGate
#check EffectiveEncoding.LabelGate.value
set_option pp.universes false in #print axioms EffectiveEncoding.LabelGate.value
#check EffectiveEncoding.labelCircuit
set_option pp.universes false in #print axioms EffectiveEncoding.labelCircuit
#check EffectiveEncoding.wireLabels
set_option pp.universes false in #print axioms EffectiveEncoding.wireLabels
#check EffectiveEncoding.compileLabels
set_option pp.universes false in #print axioms EffectiveEncoding.compileLabels
#check EffectiveEncoding.compileLabelWord
set_option pp.universes false in #print axioms EffectiveEncoding.compileLabelWord
#check EffectiveEncoding.adjacentSwapCode
set_option pp.universes false in #print axioms EffectiveEncoding.adjacentSwapCode
#check EffectiveEncoding.adjacentRotationCode
set_option pp.universes false in #print axioms EffectiveEncoding.adjacentRotationCode
#check EffectiveEncoding.orientedRotationCode
set_option pp.universes false in #print axioms EffectiveEncoding.orientedRotationCode
#check EffectiveEncoding.otherWires
set_option pp.universes false in #print axioms EffectiveEncoding.otherWires
#check EffectiveEncoding.differingWire
set_option pp.universes false in #print axioms EffectiveEncoding.differingWire
#check EffectiveEncoding.moveCode
set_option pp.universes false in #print axioms EffectiveEncoding.moveCode
#check EffectiveEncoding.swapCode
set_option pp.universes false in #print axioms EffectiveEncoding.swapCode
#check EffectiveEncoding.rotationCode
set_option pp.universes false in #print axioms EffectiveEncoding.rotationCode
#check EffectiveEncoding.GateCode.representative
set_option pp.universes false in #print axioms EffectiveEncoding.GateCode.representative
#check EffectiveEncoding.GateCode.globalPhase
set_option pp.universes false in #print axioms EffectiveEncoding.GateCode.globalPhase
#check EffectiveEncoding.representativeCircuit
set_option pp.universes false in #print axioms EffectiveEncoding.representativeCircuit
#check EffectiveEncoding.wordPhase
set_option pp.universes false in #print axioms EffectiveEncoding.wordPhase
#check EffectiveEncoding.descriptorSynthesis
set_option pp.universes false in #print axioms EffectiveEncoding.descriptorSynthesis
#check EffectiveEncoding.extractionPrecision
set_option pp.universes false in #print axioms EffectiveEncoding.extractionPrecision
#check EffectiveEncoding.numericalExtractionCode
set_option pp.universes false in #print axioms EffectiveEncoding.numericalExtractionCode
#check EffectiveEncoding.descriptorArithmeticOperations
set_option pp.universes false in #print axioms EffectiveEncoding.descriptorArithmeticOperations
#check EffectiveEncoding.gateArithmeticOperations
set_option pp.universes false in #print axioms EffectiveEncoding.gateArithmeticOperations
#check EffectiveEncoding.extractionArithmeticOperations
set_option pp.universes false in #print axioms EffectiveEncoding.extractionArithmeticOperations
#check EffectiveEncoding.countProgram
set_option pp.universes false in #print axioms EffectiveEncoding.countProgram
#check EffectiveEncoding.indexedCount
set_option pp.universes false in #print axioms EffectiveEncoding.indexedCount
#check EffectiveEncoding.explicitOthers
set_option pp.universes false in #print axioms EffectiveEncoding.explicitOthers
#check EffectiveEncoding.integerIndexedCode
set_option pp.universes false in #print axioms EffectiveEncoding.integerIndexedCode
#check EffectiveEncoding.occupiedPivot
set_option pp.universes false in #print axioms EffectiveEncoding.occupiedPivot
#check EffectiveEncoding.branchEmbedding
set_option pp.universes false in #print axioms EffectiveEncoding.branchEmbedding
#check EffectiveEncoding.pivotCoordinates
set_option pp.universes false in #print axioms EffectiveEncoding.pivotCoordinates
#check EffectiveEncoding.pivotEmbedding
set_option pp.universes false in #print axioms EffectiveEncoding.pivotEmbedding
#check EffectiveEncoding.branchCode
set_option pp.universes false in #print axioms EffectiveEncoding.branchCode
#check EffectiveEncoding.RawCode
set_option pp.universes false in #print axioms EffectiveEncoding.RawCode
#check EffectiveEncoding.mergeCode
set_option pp.universes false in #print axioms EffectiveEncoding.mergeCode
#check EffectiveEncoding.RawCode.value
set_option pp.universes false in #print axioms EffectiveEncoding.RawCode.value
#check EffectiveEncoding.RawCode.compile
set_option pp.universes false in #print axioms EffectiveEncoding.RawCode.compile
#check EffectiveEncoding.compileRaw
set_option pp.universes false in #print axioms EffectiveEncoding.compileRaw
#check EffectiveEncoding.alignmentPerm
set_option pp.universes false in #print axioms EffectiveEncoding.alignmentPerm
#check EffectiveEncoding.alignmentCode
set_option pp.universes false in #print axioms EffectiveEncoding.alignmentCode
#check EffectiveEncoding.hadRepresentative
set_option pp.universes false in #print axioms EffectiveEncoding.hadRepresentative
#check EffectiveEncoding.yRepresentative
set_option pp.universes false in #print axioms EffectiveEncoding.yRepresentative
#check EffectiveEncoding.phaseRepresentative
set_option pp.universes false in #print axioms EffectiveEncoding.phaseRepresentative
#check EffectiveEncoding.SingleCode.representative
set_option pp.universes false in #print axioms EffectiveEncoding.SingleCode.representative
#check EffectiveEncoding.SingleCode.globalPhase
set_option pp.universes false in #print axioms EffectiveEncoding.SingleCode.globalPhase
#check EffectiveEncoding.invSqrtTwoOracle
set_option pp.universes false in #print axioms EffectiveEncoding.invSqrtTwoOracle
#check EffectiveEncoding.phaseCosOracle
set_option pp.universes false in #print axioms EffectiveEncoding.phaseCosOracle
#check EffectiveEncoding.phaseSinOracle
set_option pp.universes false in #print axioms EffectiveEncoding.phaseSinOracle
#check EffectiveEncoding.quaternionStarOracle
set_option pp.universes false in #print axioms EffectiveEncoding.quaternionStarOracle
#check EffectiveEncoding.coordinatePacket
set_option pp.universes false in #print axioms EffectiveEncoding.coordinatePacket
#check EffectiveEncoding.SingleCode.quaternionOracle
set_option pp.universes false in #print axioms EffectiveEncoding.SingleCode.quaternionOracle
