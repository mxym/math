import CompletionAudit
import CompletionVerification.ReplaySupport

run_cmd (CompletionVerification.checkKinds [
  ``ExtractionCP.completelyPositive_iff_choi_posSemidef,
  ``ExtractionCP.CompletelyPositive.exists_kraus,
  ``ExtractionCP.CompletelyPositive.exists_complete_kraus,
  ``ExtractionCP.choiKraus_apply,
  ``ExtractionCP.choiKraus_complete,
  ``ExtractionCP.completelyPositive_iff_exists_finiteKraus,
  ``ExtractionCP.completelyPositive_tracePreserving_iff_exists_complete_finiteKraus,
  ``ExtractionCP.abstract_ppt_iff_actual_protocol,
  ``ExtractionCP.actual_abstract_actual_fidelity,
  ``ExtractionCP.PPTChannel.toKrausPPTProtocol_fidelity,
  ``OperationalCompletion.exists_reserved_geometric_protocol,
  ``OperationalCompletion.reservedProtocol_isProductLocal,
  ``OperationalCompletion.reservedProtocol_guarantees,
  ``OperationalCompletion.paperReservationDivisor_log_div_sqrt,
  ``OperationalCompletion.reservationLocal_eventually_pos,
  ``OperationalCompletion.reservationMainLocal_ratio_tendsto_one,
  ``OperationalCompletion.reservationSafeCutoff_le_source,
  ``OperationalCompletion.reservedProtocol_safe_mass,
  ``OperationalCompletion.reservationSafeCutoff_gaussian,
  ``OperationalCompletion.balancedReservationPacking_ratio_tendsto_one,
  ``OperationalCompletion.balanced_reserved_family_sharp,
  ``OperationalCompletion.reserved_subcritical_rate,
  ``OperationalCompletion.reserved_gaussian_limit,
  ``OperationalCompletion.reserved_eventually_exact,
  ``OperationalCompletion.reserved_reliability_limit,
  ``OperationalCompletion.reserved_fidelity_exponent,
  ``OperationalCompletion.fidelityExponent_renyi,
  ``OperationalCompletion.optimal_fidelity_exponent,
  ``OperationalCompletion.optimal_reliability_limit,
  ``OperationalCompletion.ppt_above_faithful_rate,
  ``OperationalCompletion.ppt_above_eventualExact_rate,
  ``ExtractionDeviation.finite_iid_berryEsseen_sup,
  ``ExtractionDeviation.finite_iid_berryEsseen,
  ``ExtractionDeviation.information_iid_berryEsseen,
  ``ExtractionDeviation.density_information_berryEsseen,
  ``ExtractionDeviation.informationQuantile_berryEsseen_bracket,
  ``ExtractionDeviation.universalBlockProtocol_berryEsseen,
  ``ExtractionDeviation.protocol_berryEsseen_upper,
  ``ExtractionDeviation.universalTarget_of_log_le,
  ``ExtractionDeviation.pptTarget_log_le,
  ``ExtractionDeviation.finiteCappedTarget_achievable,
  ``ExtractionDeviation.log_natFloor_exp_bounds,
  ``ExtractionDeviation.finiteCappedTarget_log_lower,
  ``ExtractionDeviation.pptFixedErrorTarget_gaussian,
  ``ExtractionDeviation.universalFixedErrorTarget_gaussian,
  ``ExtractionDeviation.triangular_informationQuantile_gaussian,
  ``ExtractionDeviation.triangular_universal_gaussian_error,
  ``ExtractionDeviation.triangular_universal_gaussian_of_variance_floor,
  ``ExtractionSchur.cycleOperator_jucys_factorization,
  ``ExtractionSchur.jucysOperators_commute,
  ``ExtractionSchur.jucysOperators_joint_eigenspaces_span,
  ``ExtractionSchur.flatHaarAverage_jucys_product_eigenvalue,
  ``ExtractionSchur.flatHaarAverage_codimension_one_purity,
  ``ExtractionSchur.flatHaarAverage_codimension_one_purity_scaled_limit,
  ``ExtractionSchur.flatHaarAverage_codimension_one_purity_isEquivalent,
  ``ExtractionSchur.rankBudget_codimension_one_sharp_lower,
  ``ExtractionSchur.haarMinorMoment_scaled_limit,
  ``ExtractionSchur.principalMinor_projectionOverlap_bounds,
  ``ExtractionSchur.haarOverlapMoment_scaled_limit,
  ``ExtractionSchur.flatHaarAverage_purity_overlap,
  ``ExtractionSchur.flatHaarAverage_general_purity_scaled_limit,
  ``ExtractionSchur.flatHaarAverage_general_purity_isEquivalent,
  ``ExtractionSchur.flatHaarAverage_purity_scaled_limit,
  ``ExtractionSchur.rankBudget_general_sharp_lower,
  ``ExtractionSchur.cyclic_tensor_mean_lower,
  ``ExtractionSchur.haarOrbitAverage_contraction_lower,
  ``ExtractionSchur.flatHaarAverage_compressed_lower,
  ``ExtractionSchur.flatHaarAverage_positive_eigenvalue_lower,
  ``ExtractionSchur.flatHaarAverage_rank_mul_minor_le_one,
  ``ExtractionSchur.haarMinorMoment_ceil_scaled_limit,
  ``ExtractionSchur.rankBudget_general_rank_upper,
  ``ExtractionSchur.rankBudget_general_rank_scaled_limit,
  ``ExtractionSchur.rankBudget_general_rank_isEquivalent,
  ``ExtractionSchur.rankBudget_general_rank_times_purity_limit,
  ``ExtractionSchur.rankBudget_rank_scaled_limit,
  ``ExtractionSchur.rankBudget_rank_times_purity_limit,
  ``ExtractionSchur.rankBudget_general_coordinate_restriction_injective,
  ``ExtractionSchur.rankBudget_general_rank_le_descendingAvoiderCount,
  ``CircuitRecursion.su2Commutator_unitary,
  ``CircuitRecursion.unitaryCommutator_conjugate,
  ``CircuitRecursion.axisCommutator_scalar,
  ``CircuitRecursion.axisX_distance,
  ``CircuitRecursion.axisY_distance,
  ``CircuitRecursion.su2_balanced_commutator,
  ``CircuitRecursion.su2_near_identity_commutator,
  ``CircuitRecursion.zeroBits_append,
  ``CircuitRecursion.bellPairsWord_action,
  ``CircuitRecursion.bellPairsWord_length,
  ``CircuitRecursion.pairwiseCoordinates_append,
  ``CircuitRecursion.cons_eq_iff,
  ``CircuitRecursion.bellPairsVector_coordinates,
  ``CircuitRecursion.sqrt_two_pow,
  ``CircuitRecursion.bellPairs_coefficient,
  ``CircuitRecursion.bellPairsVector_standard,
  ``CircuitRecursion.letterBits_physical,
  ``CircuitRecursion.unitaryDistance_nonneg,
  ``CircuitRecursion.unitaryDistance_symm,
  ``CircuitRecursion.unitaryDistance_triangle,
  ``CircuitRecursion.unitaryDistance_mul_right,
  ``CircuitRecursion.unitaryDistance_mul_left,
  ``CircuitRecursion.unitaryDistance_star,
  ``CircuitRecursion.unitaryDistance_conjugation,
  ``CircuitRecursion.unitaryCommutator_first_error,
  ``CircuitRecursion.unitaryCommutator_second_error,
  ``CircuitRecursion.unitaryCommutator_error,
  ``CircuitRecursion.active_available,
  ``CircuitRecursion.stageCircuit_action,
  ``CircuitRecursion.bitOccupation_zero,
  ``CircuitRecursion.compressionCircuit_action,
  ``CircuitRecursion.stageCircuit_length,
  ``CircuitRecursion.compressionCircuit_length,
  ``CircuitRecursion.compressionCircuit_polynomial_bound,
  ``CircuitRecursion.conjugacyTarget_entries,
  ``CircuitRecursion.conjugacyTarget_scalar,
  ``CircuitRecursion.intertwinerMass_nonneg,
  ``CircuitRecursion.intertwinerMass_sum,
  ``CircuitRecursion.intertwinerMass_large,
  ``CircuitRecursion.rationalMaxIndex_error,
  ``CircuitRecursion.conditionedChart_denominator,
  ``CircuitRecursion.chartConjugator_action,
  ``CircuitRecursion.dyadicCircuitPrecision_error,
  ``CircuitRecursion.finiteLibrary_extraction_precision,
  ``CircuitRecursion.codeWires_available,
  ``CircuitRecursion.codeWires_step,
  ``CircuitRecursion.extendBits_injective,
  ``CircuitRecursion.coordinateIsometry_single,
  ``CircuitRecursion.run_scalar,
  ``CircuitRecursion.run_zero,
  ``CircuitRecursion.encodedBranch_extend,
  ``CircuitRecursion.shifted_occupation,
  ``CircuitRecursion.coordinateIsometry_trans,
  ``CircuitRecursion.extendVector_padding,
  ``CircuitRecursion.tailBellCircuit_action,
  ``CircuitRecursion.tailBellCircuit_length,
  ``CircuitRecursion.register_split,
  ``CircuitRecursion.extractionCircuit_coherent,
  ``CircuitRecursion.extractionCircuit_purePower,
  ``CircuitRecursion.extractionCircuit_length,
  ``CircuitRecursion.extractionCircuit_polynomial_bound,
  ``CircuitRecursion.libraryWireCircuit_value,
  ``CircuitRecursion.libraryWireCircuit_length,
  ``CircuitRecursion.libraryWireCircuit_uses,
  ``CircuitRecursion.libraryGateCompiler_error,
  ``CircuitRecursion.libraryGateCompiler_length,
  ``CircuitRecursion.libraryGateCompiler_uses,
  ``CircuitRecursion.finiteLibrary_wordApproximation,
  ``CircuitRecursion.finiteLibrary_extraction_dyadic,
  ``CircuitRecursion.instructionWordValue_append,
  ``CircuitRecursion.instructionWordValue_inverse,
  ``CircuitRecursion.subgroup_instructionWord,
  ``CircuitRecursion.dense_instructionWords,
  ``CircuitRecursion.finite_instructionNet,
  ``CircuitRecursion.uniform_instructionLength,
  ``CircuitRecursion.libraryPrecision_error,
  ``CircuitRecursion.libraryPrecision_bound,
  ``CircuitRecursion.finiteLibrary_extraction,
  ``CircuitRecursion.extractionCircuit_real_bound,
  ``CircuitRecursion.extractionCircuit_isBigO,
  ``CircuitRecursion.oracleConst_correct,
  ``CircuitRecursion.oracleMeanPlus_correct,
  ``CircuitRecursion.oracleMeanMinus_correct,
  ``CircuitRecursion.halfCosOracle_correct,
  ``CircuitRecursion.mergeAngle_bounds,
  ``CircuitRecursion.mergeCosOracle_correct,
  ``CircuitRecursion.mergeSinOracle_correct,
  ``CircuitRecursion.halvedMergeCosOracle_correct,
  ``CircuitRecursion.halfSinOracle_correct,
  ``CircuitRecursion.halvedMergeSinOracle_correct,
  ``CircuitRecursion.halfCosProgram_eval,
  ``CircuitRecursion.halfCosProgram_queries,
  ``CircuitRecursion.halfCosProgram_calls,
  ``CircuitRecursion.halfAngleDemand_exact,
  ``CircuitRecursion.active_halfAngleDemand_bound,
  ``CircuitRecursion.mergeCosProgram_eval,
  ``CircuitRecursion.mergeSinProgram_eval,
  ``CircuitRecursion.mergeCosProgram_resources,
  ``CircuitRecursion.mergeSinProgram_resources,
  ``CircuitRecursion.halfAngleDemand_ge,
  ``CircuitRecursion.mergeCosProgram_precision,
  ``CircuitRecursion.mergeSinProgram_precision,
  ``CircuitRecursion.mergePhaseProgram_correct,
  ``CircuitRecursion.mergeCosProgram_range,
  ``CircuitRecursion.mergeCosProgram_dyadic,
  ``CircuitRecursion.mergeSinProgram_dyadic,
  ``CircuitRecursion.active_mergePhaseProgram_resources,
  ``CircuitRecursion.bitPurePower_density,
  ``CircuitRecursion.bitPurePower_copywiseInput,
  ``CircuitRecursion.readoutCoordinates_physical,
  ``CircuitRecursion.codeEmbedding_mulVec,
  ``CircuitRecursion.extractionVector_readout,
  ``CircuitRecursion.garbageVector_square,
  ``CircuitRecursion.bitPurePower_square,
  ``CircuitRecursion.pureOccupationCoefficients_square,
  ``CircuitRecursion.extractionOutput_coherent,
  ``CircuitRecursion.extractionOutput_purePower,
  ``CircuitRecursion.quaternionMatrix_norm_square,
  ``CircuitRecursion.su2_sub_quaternion,
  ``CircuitRecursion.su2_distance_coordinates,
  ``CircuitRecursion.square_distance_error,
  ``CircuitRecursion.distanceScore_correct,
  ``CircuitRecursion.fixedNetWord_correct,
  ``CircuitRecursion.fixedNetWord_length,
  ``CircuitRecursion.qubitRepresentative_exists,
  ``CircuitRecursion.qubitRepresentative_spec,
  ``CircuitRecursion.gatePhase_normalized,
  ``CircuitRecursion.normalizedGate_phase,
  ``CircuitRecursion.circuitPhase_normalized,
  ``CircuitRecursion.normalizedCircuit_phase,
  ``CircuitRecursion.normalized_word_error,
  ``CircuitRecursion.normalized_word_uniform_error,
  ``CircuitRecursion.occupationMass_pos_iff,
  ``CircuitRecursion.occupationMass_ge_inverse,
  ``CircuitRecursion.occupationMass_partial_count,
  ``CircuitRecursion.occupationMass_partial_le_one,
  ``CircuitRecursion.occupationMass_partial_ge_inverse,
  ``CircuitRecursion.rational_mergeAngle_trig,
  ``CircuitRecursion.occupation_partial_mergeAngle_trig,
  ``CircuitRecursion.oracleAdd_correct,
  ``CircuitRecursion.oracleNeg_correct,
  ``CircuitRecursion.dyadic_scale,
  ``CircuitRecursion.oracleMul_correct,
  ``CircuitRecursion.oracleInv_correct,
  ``CircuitRecursion.rationalSqrtApprox_correct,
  ``CircuitRecursion.sqrt_input_error,
  ``CircuitRecursion.oracleSqrt_correct,
  ``CircuitRecursion.rationalSqrtApprox_dyadic,
  ``CircuitRecursion.rationalSqrtApprox_range,
  ``CircuitRecursion.castBits_apply,
  ``CircuitRecursion.pairwiseCoordinates_alice,
  ``CircuitRecursion.pairwiseCoordinates_bob,
  ``CircuitRecursion.codeWires_eq_original,
  ``CircuitRecursion.local_register_split,
  ``CircuitRecursion.pairwiseCoordinates_physical,
  ``CircuitRecursion.readoutCoordinates_split,
  ``CircuitRecursion.boundedWords_mem,
  ``CircuitRecursion.boundedWords_length,
  ``CircuitRecursion.precomputedNet_exists,
  ``CircuitRecursion.numericalBase_exists,
  ``CircuitRecursion.dyadic_numerator_bound,
  ``CircuitRecursion.prefixCircuit_length,
  ``CircuitRecursion.extendBits_eq_pad,
  ``CircuitRecursion.prefixCircuit_eq_lift,
  ``CircuitRecursion.extendBits_trans,
  ``CircuitRecursion.extendBits_append,
  ``CircuitRecursion.paddedVector,
  ``CircuitRecursion.prefixCircuit_action,
  ``CircuitRecursion.compressionCircuit_matrix,
  ``CircuitRecursion.compressionCircuit_coherent,
  ``CircuitRecursion.bitPurePower_expansion,
  ``CircuitRecursion.compressionCircuit_purePower,
  ``CircuitRecursion.quaternionCoordinates_bound,
  ``CircuitRecursion.quaternionCoordinates_mul,
  ``CircuitRecursion.quaternionSign_abs,
  ``CircuitRecursion.unit_product_error,
  ``CircuitRecursion.quaternionProduct_error,
  ``CircuitRecursion.quaternionProduct_cast,
  ``CircuitRecursion.quaternionOracleMul_correct,
  ``CircuitRecursion.quaternionOracleOne_correct,
  ``CircuitRecursion.quaternionWordOracle_correct,
  ``CircuitRecursion.wordOracleQueries_count,
  ``CircuitRecursion.wordOracleQueries_precision,
  ``CircuitRecursion.quaternionMatrix_star_mul,
  ``CircuitRecursion.quaternionMatrix_det,
  ``CircuitRecursion.normalizedQuaternion_val,
  ``CircuitRecursion.normalizedQuaternion_intertwines,
  ``CircuitRecursion.quaternion_difference,
  ``CircuitRecursion.su2_intertwiner,
  ``CircuitRecursion.intertwiner_conjugates,
  ``CircuitRecursion.unitary_two_phase_special,
  ``CircuitRecursion.qubit_phase_special,
  ``CircuitRecursion.rationalMinIndex_le,
  ``CircuitRecursion.rationalMinIndex_error,
  ``CircuitRecursion.rationalMinIndex_net_error,
  ``CircuitRecursion.castBits_rfl,
  ``CircuitRecursion.castCircuit_rfl,
  ``CircuitRecursion.castCircuit_length,
  ``CircuitRecursion.run_castCircuit,
  ``CircuitRecursion.prefix_append,
  ``CircuitRecursion.suffix_append,
  ``CircuitRecursion.single_append,
  ``CircuitRecursion.run_shift_slice,
  ``CircuitRecursion.encodedBranch_apply_append,
  ``CircuitRecursion.discardEffect_bounds,
  ``CircuitRecursion.discardEffect_pairing,
  ``CircuitRecursion.extractionOutput_fidelity_one,
  ``CircuitRecursion.extractionOutput_robust,
  ``CircuitRecursion.extractionOutput_robust_up_to_phase,
  ``CircuitRecursion.compiledExtraction_error,
  ``CircuitRecursion.compiledExtraction_fidelity,
  ``CircuitRecursion.compiledExtraction_length,
  ``CircuitRecursion.su2AsUnitary_mul,
  ``CircuitRecursion.su2AsUnitary_inv,
  ``CircuitRecursion.balancedFactors_spec,
  ``CircuitRecursion.skCorrection_value,
  ``CircuitRecursion.skCorrection_length,
  ``CircuitRecursion.skCorrection_error,
  ``CircuitRecursion.skDoubleCorrection_error,
  ``CircuitRecursion.skPairError_zero,
  ``CircuitRecursion.skPairError_nonneg,
  ``CircuitRecursion.skPairError_succ,
  ``CircuitRecursion.skPairError_small,
  ``CircuitRecursion.skPairError_precision,
  ``CircuitRecursion.skPairWord_error,
  ``CircuitRecursion.skPairWord_length,
  ``CircuitRecursion.pow_clog_two_le,
  ``CircuitRecursion.precisionDepth_length,
  ``CircuitRecursion.su2_synthesis_dyadic,
  ``CircuitRecursion.su2_inverse_conjugate,
  ``CircuitRecursion.su2_sameScalar_conjugate,
  ``CircuitRecursion.su2Conjugate_unitary,
  ``CircuitRecursion.unitaryDistance_conjugate_one,
  ``CircuitRecursion.su2_adjugate,
  ``CircuitRecursion.su2_lower_left,
  ``CircuitRecursion.su2_lower_right,
  ``CircuitRecursion.su2_normalForm,
  ``CircuitRecursion.su2_mass,
  ``CircuitRecursion.su2_scalarPart_bounds,
  ``CircuitRecursion.su2_trace,
  ``CircuitRecursion.su2_add_adjoint,
  ``CircuitRecursion.su2_distance_square,
  ``CircuitRecursion.specialUnitary_isCompact,
  ``CircuitRecursion.specialUnitary_compactSpace,
  ``CircuitRecursion.su2_uniform_instructionLength,
  ``CircuitRecursion.matrixReindex_norm,
  ``CircuitRecursion.singleWire_eq_hom,
  ``CircuitRecursion.singleWire_error,
  ``CircuitRecursion.singleWire_phase,
  ``CircuitRecursion.su2ToBool_error,
  ``CircuitRecursion.bellPairYield_feasible,
  ``CircuitRecursion.bellPairYield_maximal,
  ``CircuitRecursion.bellPairYield_floor_log4,
  ``CircuitRecursion.log4_eq_half_log2,
  ``CircuitRecursion.bellPairYield_floor,
  ``CircuitRecursion.bellPairYield_cPPT_maximal,
  ``OperationalCompletion.reservedTargets_subset_pptTargets,
  ``OperationalCompletion.reservedTargets_lower_bracket,
  ``OperationalCompletion.reservedFixedErrorTarget_gaussian,
  ``OperationalCompletion.reservationSafeCutoff_expansion,
  ``OperationalCompletion.reservedProtocol_berryEsseen,
  ``OperationalCompletion.reserved_optimal_gaussian_limit,
  ``OperationalCompletion.reserved_optimum_gaussian_error,
  ``OperationalCompletion.triangular_reserved_optimum_gaussian_error,
  ``OperationalCompletion.bellProjector_one,
  ``OperationalCompletion.protocol_fidelity_one,
  ``OperationalCompletion.density_entropy_rank_bounds,
  ``OperationalCompletion.capacityRates_nonneg,
  ``OperationalCompletion.exactAttainable_zero,
  ``OperationalCompletion.exactAttainable_subset_faithful,
  ``OperationalCompletion.faithfulAttainable_le,
  ``OperationalCompletion.exactAttainable_le,
  ``OperationalCompletion.faithfulAttainable_below,
  ``OperationalCompletion.exactAttainable_below,
  ``OperationalCompletion.faithfulCapacity_eq,
  ``OperationalCompletion.exactCapacity_eq,
  ``OperationalCompletion.productLocal_capacities,
  ``OperationalCompletion.cPPT_capacities,
  ``OperationalCompletion.finiteLOCC_capacities,
  ``OperationalCompletion.density_ensemble_integrable,
  ``OperationalCompletion.probabilityAverage_density,
  ``OperationalCompletion.fidelity_probabilityAverage,
  ``OperationalCompletion.guarantee_le_probabilityAverage,
  ``OperationalCompletion.physical_probability_ensemble_bound,
  ``OperationalCompletion.measurable_physical_ensemble_bound,
  ``OperationalCompletion.reservedTotalLoss_nonneg,
  ``OperationalCompletion.reservedProtocol_gaussian_error,
  ``OperationalCompletion.triangular_reserved_gaussian_error,
  ``OperationalCompletion.pureSupportRank_log_le,
  ``OperationalCompletion.reservedTotalLoss_dimension_bound,
  ``OperationalCompletion.dimensionScale_sq,
  ``OperationalCompletion.dimensionScale_tendsto,
  ``OperationalCompletion.sqrt_block_div_dimension_tendsto,
  ``OperationalCompletion.variance_normalization_lower,
  ``OperationalCompletion.lyapunov_shrinking_bound,
  ``OperationalCompletion.shrinking_variance_numerical_conditions,
  ``OperationalCompletion.triangular_reserved_gaussian_shrinking_variance,
  ``ExtractionLOCC.Tree.leafKraus_complete,
  ``ExtractionLOCC.Tree.channel_completelyPositive,
  ``ExtractionLOCC.Tree.channel_tracePreserving,
  ``ExtractionLOCC.Tree.channel_done,
  ``ExtractionLOCC.Tree.channel_alice,
  ``ExtractionLOCC.Tree.channel_bob,
  ``ExtractionLOCC.Tree.pt_identity,
  ``ExtractionLOCC.Tree.channel_pt_completelyPositive,
  ``ExtractionLOCC.Tree.ptLeafKraus_complete,
  ``ExtractionLOCC.Tree.product_channel,
  ``ExtractionLOCC.Tree.protocol_apply,
  ``ExtractionLOCC.IsFiniteLOCC.completelyPositive,
  ``ExtractionLOCC.IsFiniteLOCC.tracePreserving,
  ``ExtractionLOCC.IsFiniteLOCC.pt_completelyPositive,
  ``ExtractionLOCC.tree_isFiniteLOCCProtocol,
  ``ExtractionLOCC.productLocal_isFiniteLOCCProtocol,
  ``ExtractionLOCC.IsFiniteLOCC.exists_actual_protocol,
  ``ExtractionLOCC.choi_injective,
  ``ExtractionLOCC.continuous_evaluation,
  ``ExtractionLOCC.isClosed_completelyPositive,
  ``ExtractionLOCC.isClosed_tracePreserving,
  ``ExtractionLOCC.choi_ptConjugate,
  ``ExtractionLOCC.continuous_choi_ptConjugate,
  ``ExtractionLOCC.isClosed_pt_completelyPositive,
  ``ExtractionLOCC.IsFiniteLOCC.isClosureLOCC,
  ``ExtractionLOCC.IsClosureLOCC.completelyPositive,
  ``ExtractionLOCC.IsClosureLOCC.tracePreserving,
  ``ExtractionLOCC.IsClosureLOCC.pt_completelyPositive,
  ``ExtractionLOCC.finiteLOCC_isClosureLOCCProtocol,
  ``ExtractionLOCC.productLocal_isClosureLOCCProtocol,
  ``ExtractionLOCC.IsClosureLOCC.exists_actual_protocol,
  ``ExtractionLOCC.Instrument.outcome_completelyPositive,
  ``ExtractionLOCC.Instrument.ofCP_outcomeMap,
  ``ExtractionLOCC.Tree.channel_aliceInstrument,
  ``ExtractionLOCC.Tree.channel_bobInstrument,
  ``ExtractionRains.choi_measurePrepare,
  ``ExtractionRains.measurePrepare_completelyPositive,
  ``ExtractionRains.failureState_posSemidef,
  ``ExtractionRains.failureState_trace,
  ``ExtractionRains.channel_completelyPositive,
  ``ExtractionRains.channel_tracePreserving,
  ``ExtractionRains.bell_failureState_trace,
  ``ExtractionRains.channel_target_overlap,
  ``ExtractionRains.plusProjection_posSemidef,
  ``ExtractionRains.minusProjection_posSemidef,
  ``ExtractionRains.plusEffect_posSemidef,
  ``ExtractionRains.minusEffect_posSemidef,
  ``ExtractionRains.pt_channel_formula,
  ``ExtractionRains.pt_channel_decomposition,
  ``ExtractionRains.channel_pt_completelyPositive,
  ``ExtractionRains.protocol_apply,
  ``ExtractionRains.protocol_targetEffect,
  ``ExtractionRains.protocol_fidelity,
  ``ExtractionRains.rainsEffect_exists_actual_protocol,
  ``ExtractionRains.rainsEffect_iff_actual_protocol_effect,
  ``ExtractionSchur.errorRankBudgetMaximum_attained,
  ``ExtractionSchur.errorRankBudgetMaximum_full_rank,
  ``ExtractionSchur.errorRankBudgetMaximum_isGreatest,
  ``ExtractionSchur.errorRankBudgetMaximum_log_limit,
  ``ExtractionSchur.exactRankBudgetMaximum_attained,
  ``ExtractionSchur.exactRankBudgetMaximum_bounds,
  ``ExtractionSchur.exactRankBudgetMaximum_eventually_local,
  ``ExtractionSchur.exactRankBudgetMaximum_full_rank,
  ``ExtractionSchur.exactRankBudgetMaximum_log_correction_limit,
  ``ExtractionSchur.exact_fixedOrbit_physical_budget,
  ``ExtractionSchur.flatOrbitErrorMaximum_attained,
  ``ExtractionSchur.flatOrbitErrorMaximum_bounds,
  ``ExtractionSchur.flatOrbitErrorMaximum_full_rank,
  ``ExtractionSchur.flatOrbitErrorMaximum_isGreatest,
  ``ExtractionSchur.flatOrbitErrorMaximum_log_limit,
  ``ExtractionSchur.flatOrbit_full_rank_minimax,
  ``ExtractionSchur.flatOrbit_minimax_profile_bounds,
  ``ExtractionSchur.flatOrbit_target_uniform_minimax,
  ``ExtractionSchur.flatOrbit_target_uniform_relative_error,
  ``ExtractionSchur.orbitExactMaximum_attained,
  ``ExtractionSchur.orbitExactMaximum_bounds,
  ``ExtractionSchur.orbitExactMaximum_eventually_local,
  ``ExtractionSchur.orbitExactMaximum_full_rank,
  ``ExtractionSchur.orbitExactMaximum_isGreatest,
  ``ExtractionSchur.orbitExactMaximum_log_correction_limit,
  ``ExtractionSchur.rankBudgetEta_limit,
  ``ExtractionSchur.rankBudgetPacking_ratio_limit,
  ``ExtractionSchur.rankBudget_class_minimax_finite,
  ``ExtractionSchur.rankBudget_completelyPPT_eq_minimaxValue,
  ``ExtractionSchur.rankBudget_full_rank_minimax,
  ``ExtractionSchur.rankBudget_physical_class_chain,
  ``ExtractionSchur.rankBudget_physical_relative_bound,
  ``ExtractionSchur.rankBudget_target_uniform_minimax,
  ``ExtractionSchur.rankBudget_target_uniform_relative_error,
  ``ExtractionAPPT.trace_cfc,
  ``ExtractionAPPT.quantumEntropy_eq_spectral,
  ``ExtractionAPPT.continuousOn_quantumEntropy,
  ``ExtractionAPPT.cfc_submatrix,
  ``ExtractionAPPT.quantumEntropy_submatrix,
  ``ExtractionAPPT.flatten_density,
  ``ExtractionAPPT.flatten_entropy,
  ``ExtractionAPPT.flatten_spectral_entropy,
  ``ExtractionAPPT.continuousOn_appt_entropy,
  ``ExtractionAPPT.exists_appt_entropy_isLeast,
  ``ExtractionAPPT.exists_appt_entropy_eq_inf,
  ``ExtractionAPPT.physicalCapacity_eq,
  ``ExtractionAPPT.physicalCapacity_eq_cPPT,
  ``ExtractionAPPT.exists_appt_capacity_isGreatest,
  ``ExtractionAPPT.exists_appt_capacity_eq_sup,
  ``ExtractionAPPT.apptMaxCapacity_eq,
  ``ExtractionAPPT.exists_appt_purity_maximizer,
  ``ExtractionAPPT.entropy_ge_neg_log_collision,
  ``ExtractionAPPT.density_entropy_purity_bound,
  ``ExtractionAPPT.physicalCapacity_le_purity,
  ``ExtractionAPPT.apptMaxCapacity_le_puritySup,
  ``ExtractionAPPT.physicalCapacity_eq_closureLOCC,
  ``ExtractionAPPT.schmidt_product_le_half,
  ``ExtractionAPPT.schmidtSigned_lower,
  ``ExtractionAPPT.pure_partialTranspose_lower,
  ``ExtractionAPPT.spikeState_density,
  ``ExtractionAPPT.spikeState_absolutelyPPT,
  ``ExtractionAPPT.spikeState_mem_appt,
  ``ExtractionAPPT.projection_spectrum_zero_one,
  ``ExtractionAPPT.cfc_affine_projection,
  ``ExtractionAPPT.quantumEntropy_affine_rankOne,
  ``ExtractionAPPT.spikeState_entropy,
  ``ExtractionAPPT.spikeState_capacity,
  ``ExtractionAPPT.spike_capacity_le_apptMax,
  ``ExtractionAPPT.spike_rate_error_bounds,
  ``ExtractionAPPT.spikeState_capacity_error_bounds,
  ``ExtractionAPPT.spike_capacity_coefficient_limit,
  ``ExtractionAPPT.normalized_log_budget_limit,
  ``ExtractionAPPT.balanced_purity_excess_limit,
  ``ExtractionAPPT.balanced_purity_capacity_budget_limit,
  ``ExtractionAPPT.balanced_apptMaxCapacity_upper,
  ``ExtractionAPPT.balanced_apptMaxCapacity_upper_remainder,
  ``ExtractionAPPT.spikeState_scaled_capacity_limit,
  ``ExtractionAPPT.balanced_apptMaxCapacity_lower,
  ``ExtractionAPPT.balanced_apptMaxCapacity_first_order_bounds,
  ``OperationalCompletion.heterogeneous_projection_protocol,
  ``SpectralProtocol.oneShotSpectralEnvelope_actual_lower,
  ``SpectralProtocol.oneShotSpectralEnvelope_actual_upper,
  ``MinimaxProfile.tensorProjection_rank_le,
  ``MinimaxProfile.tensorProjection_mass_ge,
  ``ExtractionSchur.haarOrbitAverage_range,
  ``ExtractionSchur.haarOrbitAverage_rank,
  ``ExtractionSchur.haarOrbitAverage_trace_square,
  ``ExtractionSchur.haarMinorMoment_product
] [
  ``ExtractionCP.amplification,
  ``ExtractionCP.CompletelyPositive,
  ``ExtractionCP.TracePreserving,
  ``ExtractionCP.choi,
  ``ExtractionCP.choiKraus,
  ``ExtractionCP.ptConjugate,
  ``ExtractionCP.PPTChannel,
  ``ExtractionCP.PPTChannel.toKrausPPTProtocol,
  ``ExtractionCP.ofKrausPPTProtocol,
  ``OperationalCompletion.reservedProtocol,
  ``OperationalCompletion.reservationLocal,
  ``OperationalCompletion.reservationMainLocal,
  ``OperationalCompletion.paperReservationDivisor,
  ``OperationalCompletion.paperReservedPacking,
  ``OperationalCompletion.reservationLoss,
  ``OperationalCompletion.reservationSafeCutoff,
  ``OperationalCompletion.balancedReservationPacking,
  ``OperationalCompletion.balancedReservedWidth,
  ``OperationalCompletion.fidelityExponent,
  ``OperationalCompletion.protocolOptimum,
  ``ExtractionDeviation.berryEsseenConstant,
  ``ExtractionDeviation.informationBerryEsseenError,
  ``ExtractionDeviation.compressionLoss,
  ``ExtractionDeviation.finiteCappedTarget,
  ``ExtractionDeviation.pptTargets,
  ``ExtractionDeviation.universalTargets,
  ``ExtractionDeviation.pptFixedErrorTarget,
  ``ExtractionDeviation.universalFixedErrorTarget,
  ``ExtractionDeviation.dimensionLossBound,
  ``ExtractionSchur.projectedGram,
  ``ExtractionSchur.projectionOverlap,
  ``ExtractionSchur.haarOverlapMoment,
  ``ExtractionSchur.compressionLinear,
  ``ExtractionSchur.haarTwirlLinear,
  ``ExtractionSchur.cyclicTensorMean,
  ``ExtractionSchur.HasDescendingSubsequence,
  ``ExtractionSchur.DescendingAvoider,
  ``ExtractionSchur.descendingAvoiderCount,
  ``CircuitRecursion.compressionCircuit,
  ``CircuitRecursion.bitPurePower,
  ``CircuitRecursion.bellPairYield,
  ``CircuitRecursion.extractionCircuit,
  ``CircuitRecursion.extractionOutput,
  ``CircuitRecursion.approximateExtractionOutput,
  ``CircuitRecursion.physicalLocalReadoutCoordinates,
  ``CircuitRecursion.readoutCoordinates,
  ``CircuitRecursion.localReadoutCoordinates,
  ``CircuitRecursion.codePairCoordinates,
  ``CircuitRecursion.usesFiniteLibrary,
  ``CircuitRecursion.instructionWordValue,
  ``CircuitRecursion.skPairWord,
  ``CircuitRecursion.libraryGateCompiler,
  ``CircuitRecursion.libraryPrecision,
  ``CircuitRecursion.circuitPhase,
  ``CircuitRecursion.conjugacyFrame,
  ``CircuitRecursion.conjugacyTarget,
  ``CircuitRecursion.intertwinerMass,
  ``CircuitRecursion.rationalMaxIndex,
  ``CircuitRecursion.chartConjugator,
  ``CircuitRecursion.RationalOracle,
  ``CircuitRecursion.Approximates,
  ``CircuitRecursion.oracleAdd,
  ``CircuitRecursion.oracleNeg,
  ``CircuitRecursion.oracleMul,
  ``CircuitRecursion.oracleInv,
  ``CircuitRecursion.rationalSqrtApprox,
  ``CircuitRecursion.oracleSqrt,
  ``CircuitRecursion.oracleConst,
  ``CircuitRecursion.oracleMeanPlus,
  ``CircuitRecursion.oracleMeanMinus,
  ``CircuitRecursion.halfCosOracle,
  ``CircuitRecursion.mergeCosOracle,
  ``CircuitRecursion.mergeSinOracle,
  ``CircuitRecursion.halfSinOracle,
  ``CircuitRecursion.ScalarProgram,
  ``CircuitRecursion.ScalarProgram.eval,
  ``CircuitRecursion.ScalarProgram.queries,
  ``CircuitRecursion.ScalarProgram.sqrtCalls,
  ``CircuitRecursion.ScalarProgram.rationalCalls,
  ``CircuitRecursion.halfCosProgram,
  ``CircuitRecursion.halfAngleDemand,
  ``CircuitRecursion.mergeCosProgram,
  ``CircuitRecursion.mergeSinProgram,
  ``CircuitRecursion.ScalarProgram.maxRootPrecision,
  ``CircuitRecursion.quaternionCoordinates,
  ``CircuitRecursion.quaternionRight,
  ``CircuitRecursion.quaternionSign,
  ``CircuitRecursion.quaternionProduct,
  ``CircuitRecursion.QuaternionOracle,
  ``CircuitRecursion.QApproximates,
  ``CircuitRecursion.quaternionOracleMul,
  ``CircuitRecursion.quaternionOracleOne,
  ``CircuitRecursion.quaternionWordOracle,
  ``CircuitRecursion.wordOracleQueries,
  ``CircuitRecursion.rationalSquaredDistance,
  ``CircuitRecursion.distanceScore,
  ``CircuitRecursion.fixedNetWord,
  ``CircuitRecursion.boundedWords,
  ``CircuitRecursion.DyadicQuaternionOracle,
  ``CircuitRecursion.dyadicQuaternionOracle,
  ``CircuitRecursion.DyadicQApproximates,
  ``OperationalCompletion.reservedTargets,
  ``OperationalCompletion.reservedFixedErrorTarget,
  ``OperationalCompletion.reservedTotalLoss,
  ``OperationalCompletion.faithfulAttainableRates,
  ``OperationalCompletion.exactAttainableRates,
  ``OperationalCompletion.faithfulCapacity,
  ``OperationalCompletion.exactCapacity,
  ``OperationalCompletion.protocolFidelityLinear,
  ``OperationalCompletion.matrixTraceLinear,
  ``OperationalCompletion.probabilityAverage,
  ``OperationalCompletion.dimensionScale,
  ``ExtractionLOCC.Tree,
  ``ExtractionLOCC.Tree.Leaf,
  ``ExtractionLOCC.Tree.leafAlice,
  ``ExtractionLOCC.Tree.leafBob,
  ``ExtractionLOCC.Tree.leafKraus,
  ``ExtractionLOCC.Tree.channel,
  ``ExtractionLOCC.Tree.ptLeafKraus,
  ``ExtractionLOCC.Tree.product,
  ``ExtractionLOCC.Tree.pptChannel,
  ``ExtractionLOCC.Tree.protocol,
  ``ExtractionLOCC.IsFiniteLOCC,
  ``ExtractionLOCC.IsFiniteLOCCProtocol,
  ``ExtractionLOCC.Instrument,
  ``ExtractionLOCC.Instrument.ofCP,
  ``ExtractionLOCC.Instrument.outcomeMap,
  ``ExtractionLOCC.Tree.aliceInstrument,
  ``ExtractionLOCC.Tree.bobInstrument,
  ``ExtractionLOCC.coefficientTopology,
  ``ExtractionLOCC.IsClosureLOCC,
  ``ExtractionLOCC.IsClosureLOCCProtocol,
  ``ExtractionRains.measurePrepare,
  ``ExtractionRains.failureState,
  ``ExtractionRains.channel,
  ``ExtractionRains.plusProjection,
  ``ExtractionRains.minusProjection,
  ``ExtractionRains.plusEffect,
  ``ExtractionRains.minusEffect,
  ``ExtractionRains.pptChannel,
  ``ExtractionRains.protocol,
  ``ExtractionSchur.RankBudgetInput,
  ``ExtractionSchur.rankBudgetClassMinimax,
  ``ExtractionSchur.rankBudgetProjection,
  ``ExtractionSchur.physicalHaarAverage,
  ``ExtractionSchur.rankBudgetOrbitInput,
  ``ExtractionSchur.RankProtocolClass,
  ``ExtractionSchur.RankProtocolClass.Allows,
  ``ExtractionSchur.rankBudgetPhysicalMinimax,
  ``ExtractionSchur.rankBudgetCollisionWidth,
  ``ExtractionSchur.rankBudgetWidth,
  ``ExtractionSchur.rankBudgetPacking,
  ``ExtractionSchur.rankBudgetEta,
  ``ExtractionSchur.exactRankBudgetTargets,
  ``ExtractionSchur.errorRankBudgetTargets,
  ``ExtractionSchur.exactRankBudgetMaximum,
  ``ExtractionSchur.errorRankBudgetMaximum,
  ``ExtractionSchur.rankBudgetLogScale,
  ``ExtractionSchur.densityOrbitInput,
  ``ExtractionSchur.orbitExactTargets,
  ``ExtractionSchur.orbitExactMaximum,
  ``ExtractionSchur.flatOrbitPhysicalMinimax,
  ``ExtractionSchur.flatOrbitErrorTargets,
  ``ExtractionSchur.flatOrbitErrorMaximum,
  ``ExtractionAPPT.quantumEntropy,
  ``ExtractionAPPT.flatten,
  ``ExtractionAPPT.apptEntropyValues,
  ``ExtractionAPPT.apptMinEntropy,
  ``ExtractionAPPT.physicalCapacity,
  ``ExtractionAPPT.apptCapacityValues,
  ``ExtractionAPPT.apptMaxCapacity,
  ``ExtractionAPPT.spikeState,
  ``ExtractionAPPT.purityCapacityBudget,
  ``MinimaxProfile.KrausPPTProtocol,
  ``MinimaxProfile.tensorInput
])

#check ExtractionCP.completelyPositive_iff_choi_posSemidef
#print axioms ExtractionCP.completelyPositive_iff_choi_posSemidef
#check ExtractionCP.CompletelyPositive.exists_kraus
#print axioms ExtractionCP.CompletelyPositive.exists_kraus
#check ExtractionCP.CompletelyPositive.exists_complete_kraus
#print axioms ExtractionCP.CompletelyPositive.exists_complete_kraus
#check ExtractionCP.choiKraus_apply
#print axioms ExtractionCP.choiKraus_apply
#check ExtractionCP.choiKraus_complete
#print axioms ExtractionCP.choiKraus_complete
#check ExtractionCP.completelyPositive_iff_exists_finiteKraus
#print axioms ExtractionCP.completelyPositive_iff_exists_finiteKraus
#check ExtractionCP.completelyPositive_tracePreserving_iff_exists_complete_finiteKraus
#print axioms ExtractionCP.completelyPositive_tracePreserving_iff_exists_complete_finiteKraus
#check ExtractionCP.abstract_ppt_iff_actual_protocol
#print axioms ExtractionCP.abstract_ppt_iff_actual_protocol
#check ExtractionCP.actual_abstract_actual_fidelity
#print axioms ExtractionCP.actual_abstract_actual_fidelity
#check ExtractionCP.PPTChannel.toKrausPPTProtocol_fidelity
#print axioms ExtractionCP.PPTChannel.toKrausPPTProtocol_fidelity
#check OperationalCompletion.exists_reserved_geometric_protocol
#print axioms OperationalCompletion.exists_reserved_geometric_protocol
#check OperationalCompletion.reservedProtocol_isProductLocal
#print axioms OperationalCompletion.reservedProtocol_isProductLocal
#check OperationalCompletion.reservedProtocol_guarantees
#print axioms OperationalCompletion.reservedProtocol_guarantees
#check OperationalCompletion.paperReservationDivisor_log_div_sqrt
#print axioms OperationalCompletion.paperReservationDivisor_log_div_sqrt
#check OperationalCompletion.reservationLocal_eventually_pos
#print axioms OperationalCompletion.reservationLocal_eventually_pos
#check OperationalCompletion.reservationMainLocal_ratio_tendsto_one
#print axioms OperationalCompletion.reservationMainLocal_ratio_tendsto_one
#check OperationalCompletion.reservationSafeCutoff_le_source
#print axioms OperationalCompletion.reservationSafeCutoff_le_source
#check OperationalCompletion.reservedProtocol_safe_mass
#print axioms OperationalCompletion.reservedProtocol_safe_mass
#check OperationalCompletion.reservationSafeCutoff_gaussian
#print axioms OperationalCompletion.reservationSafeCutoff_gaussian
#check OperationalCompletion.balancedReservationPacking_ratio_tendsto_one
#print axioms OperationalCompletion.balancedReservationPacking_ratio_tendsto_one
#check OperationalCompletion.balanced_reserved_family_sharp
#print axioms OperationalCompletion.balanced_reserved_family_sharp
#check OperationalCompletion.reserved_subcritical_rate
#print axioms OperationalCompletion.reserved_subcritical_rate
#check OperationalCompletion.reserved_gaussian_limit
#print axioms OperationalCompletion.reserved_gaussian_limit
#check OperationalCompletion.reserved_eventually_exact
#print axioms OperationalCompletion.reserved_eventually_exact
#check OperationalCompletion.reserved_reliability_limit
#print axioms OperationalCompletion.reserved_reliability_limit
#check OperationalCompletion.reserved_fidelity_exponent
#print axioms OperationalCompletion.reserved_fidelity_exponent
#check OperationalCompletion.fidelityExponent_renyi
#print axioms OperationalCompletion.fidelityExponent_renyi
#check OperationalCompletion.optimal_fidelity_exponent
#print axioms OperationalCompletion.optimal_fidelity_exponent
#check OperationalCompletion.optimal_reliability_limit
#print axioms OperationalCompletion.optimal_reliability_limit
#check OperationalCompletion.ppt_above_faithful_rate
#print axioms OperationalCompletion.ppt_above_faithful_rate
#check OperationalCompletion.ppt_above_eventualExact_rate
#print axioms OperationalCompletion.ppt_above_eventualExact_rate
#check ExtractionDeviation.finite_iid_berryEsseen_sup
#print axioms ExtractionDeviation.finite_iid_berryEsseen_sup
#check ExtractionDeviation.finite_iid_berryEsseen
#print axioms ExtractionDeviation.finite_iid_berryEsseen
#check ExtractionDeviation.information_iid_berryEsseen
#print axioms ExtractionDeviation.information_iid_berryEsseen
#check ExtractionDeviation.density_information_berryEsseen
#print axioms ExtractionDeviation.density_information_berryEsseen
#check ExtractionDeviation.informationQuantile_berryEsseen_bracket
#print axioms ExtractionDeviation.informationQuantile_berryEsseen_bracket
#check ExtractionDeviation.universalBlockProtocol_berryEsseen
#print axioms ExtractionDeviation.universalBlockProtocol_berryEsseen
#check ExtractionDeviation.protocol_berryEsseen_upper
#print axioms ExtractionDeviation.protocol_berryEsseen_upper
#check ExtractionDeviation.universalTarget_of_log_le
#print axioms ExtractionDeviation.universalTarget_of_log_le
#check ExtractionDeviation.pptTarget_log_le
#print axioms ExtractionDeviation.pptTarget_log_le
#check ExtractionDeviation.finiteCappedTarget_achievable
#print axioms ExtractionDeviation.finiteCappedTarget_achievable
#check ExtractionDeviation.log_natFloor_exp_bounds
#print axioms ExtractionDeviation.log_natFloor_exp_bounds
#check ExtractionDeviation.finiteCappedTarget_log_lower
#print axioms ExtractionDeviation.finiteCappedTarget_log_lower
#check ExtractionDeviation.pptFixedErrorTarget_gaussian
#print axioms ExtractionDeviation.pptFixedErrorTarget_gaussian
#check ExtractionDeviation.universalFixedErrorTarget_gaussian
#print axioms ExtractionDeviation.universalFixedErrorTarget_gaussian
#check ExtractionDeviation.triangular_informationQuantile_gaussian
#print axioms ExtractionDeviation.triangular_informationQuantile_gaussian
#check ExtractionDeviation.triangular_universal_gaussian_error
#print axioms ExtractionDeviation.triangular_universal_gaussian_error
#check ExtractionDeviation.triangular_universal_gaussian_of_variance_floor
#print axioms ExtractionDeviation.triangular_universal_gaussian_of_variance_floor
#check ExtractionSchur.cycleOperator_jucys_factorization
#print axioms ExtractionSchur.cycleOperator_jucys_factorization
#check ExtractionSchur.jucysOperators_commute
#print axioms ExtractionSchur.jucysOperators_commute
#check ExtractionSchur.jucysOperators_joint_eigenspaces_span
#print axioms ExtractionSchur.jucysOperators_joint_eigenspaces_span
#check ExtractionSchur.flatHaarAverage_jucys_product_eigenvalue
#print axioms ExtractionSchur.flatHaarAverage_jucys_product_eigenvalue
#check ExtractionSchur.flatHaarAverage_codimension_one_purity
#print axioms ExtractionSchur.flatHaarAverage_codimension_one_purity
#check ExtractionSchur.flatHaarAverage_codimension_one_purity_scaled_limit
#print axioms ExtractionSchur.flatHaarAverage_codimension_one_purity_scaled_limit
#check ExtractionSchur.flatHaarAverage_codimension_one_purity_isEquivalent
#print axioms ExtractionSchur.flatHaarAverage_codimension_one_purity_isEquivalent
#check ExtractionSchur.rankBudget_codimension_one_sharp_lower
#print axioms ExtractionSchur.rankBudget_codimension_one_sharp_lower
#check ExtractionSchur.haarMinorMoment_scaled_limit
#print axioms ExtractionSchur.haarMinorMoment_scaled_limit
#check ExtractionSchur.principalMinor_projectionOverlap_bounds
#print axioms ExtractionSchur.principalMinor_projectionOverlap_bounds
#check ExtractionSchur.haarOverlapMoment_scaled_limit
#print axioms ExtractionSchur.haarOverlapMoment_scaled_limit
#check ExtractionSchur.flatHaarAverage_purity_overlap
#print axioms ExtractionSchur.flatHaarAverage_purity_overlap
#check ExtractionSchur.flatHaarAverage_general_purity_scaled_limit
#print axioms ExtractionSchur.flatHaarAverage_general_purity_scaled_limit
#check ExtractionSchur.flatHaarAverage_general_purity_isEquivalent
#print axioms ExtractionSchur.flatHaarAverage_general_purity_isEquivalent
#check ExtractionSchur.flatHaarAverage_purity_scaled_limit
#print axioms ExtractionSchur.flatHaarAverage_purity_scaled_limit
#check ExtractionSchur.rankBudget_general_sharp_lower
#print axioms ExtractionSchur.rankBudget_general_sharp_lower
#check ExtractionSchur.cyclic_tensor_mean_lower
#print axioms ExtractionSchur.cyclic_tensor_mean_lower
#check ExtractionSchur.haarOrbitAverage_contraction_lower
#print axioms ExtractionSchur.haarOrbitAverage_contraction_lower
#check ExtractionSchur.flatHaarAverage_compressed_lower
#print axioms ExtractionSchur.flatHaarAverage_compressed_lower
#check ExtractionSchur.flatHaarAverage_positive_eigenvalue_lower
#print axioms ExtractionSchur.flatHaarAverage_positive_eigenvalue_lower
#check ExtractionSchur.flatHaarAverage_rank_mul_minor_le_one
#print axioms ExtractionSchur.flatHaarAverage_rank_mul_minor_le_one
#check ExtractionSchur.haarMinorMoment_ceil_scaled_limit
#print axioms ExtractionSchur.haarMinorMoment_ceil_scaled_limit
#check ExtractionSchur.rankBudget_general_rank_upper
#print axioms ExtractionSchur.rankBudget_general_rank_upper
#check ExtractionSchur.rankBudget_general_rank_scaled_limit
#print axioms ExtractionSchur.rankBudget_general_rank_scaled_limit
#check ExtractionSchur.rankBudget_general_rank_isEquivalent
#print axioms ExtractionSchur.rankBudget_general_rank_isEquivalent
#check ExtractionSchur.rankBudget_general_rank_times_purity_limit
#print axioms ExtractionSchur.rankBudget_general_rank_times_purity_limit
#check ExtractionSchur.rankBudget_rank_scaled_limit
#print axioms ExtractionSchur.rankBudget_rank_scaled_limit
#check ExtractionSchur.rankBudget_rank_times_purity_limit
#print axioms ExtractionSchur.rankBudget_rank_times_purity_limit
#check ExtractionSchur.rankBudget_general_coordinate_restriction_injective
#print axioms ExtractionSchur.rankBudget_general_coordinate_restriction_injective
#check ExtractionSchur.rankBudget_general_rank_le_descendingAvoiderCount
#print axioms ExtractionSchur.rankBudget_general_rank_le_descendingAvoiderCount
#check CircuitRecursion.su2Commutator_unitary
#print axioms CircuitRecursion.su2Commutator_unitary
#check CircuitRecursion.unitaryCommutator_conjugate
#print axioms CircuitRecursion.unitaryCommutator_conjugate
#check CircuitRecursion.axisCommutator_scalar
#print axioms CircuitRecursion.axisCommutator_scalar
#check CircuitRecursion.axisX_distance
#print axioms CircuitRecursion.axisX_distance
#check CircuitRecursion.axisY_distance
#print axioms CircuitRecursion.axisY_distance
#check CircuitRecursion.su2_balanced_commutator
#print axioms CircuitRecursion.su2_balanced_commutator
#check CircuitRecursion.su2_near_identity_commutator
#print axioms CircuitRecursion.su2_near_identity_commutator
#check CircuitRecursion.zeroBits_append
#print axioms CircuitRecursion.zeroBits_append
#check CircuitRecursion.bellPairsWord_action
#print axioms CircuitRecursion.bellPairsWord_action
#check CircuitRecursion.bellPairsWord_length
#print axioms CircuitRecursion.bellPairsWord_length
#check CircuitRecursion.pairwiseCoordinates_append
#print axioms CircuitRecursion.pairwiseCoordinates_append
#check CircuitRecursion.cons_eq_iff
#print axioms CircuitRecursion.cons_eq_iff
#check CircuitRecursion.bellPairsVector_coordinates
#print axioms CircuitRecursion.bellPairsVector_coordinates
#check CircuitRecursion.sqrt_two_pow
#print axioms CircuitRecursion.sqrt_two_pow
#check CircuitRecursion.bellPairs_coefficient
#print axioms CircuitRecursion.bellPairs_coefficient
#check CircuitRecursion.bellPairsVector_standard
#print axioms CircuitRecursion.bellPairsVector_standard
#check CircuitRecursion.letterBits_physical
#print axioms CircuitRecursion.letterBits_physical
#check CircuitRecursion.unitaryDistance_nonneg
#print axioms CircuitRecursion.unitaryDistance_nonneg
#check CircuitRecursion.unitaryDistance_symm
#print axioms CircuitRecursion.unitaryDistance_symm
#check CircuitRecursion.unitaryDistance_triangle
#print axioms CircuitRecursion.unitaryDistance_triangle
#check CircuitRecursion.unitaryDistance_mul_right
#print axioms CircuitRecursion.unitaryDistance_mul_right
#check CircuitRecursion.unitaryDistance_mul_left
#print axioms CircuitRecursion.unitaryDistance_mul_left
#check CircuitRecursion.unitaryDistance_star
#print axioms CircuitRecursion.unitaryDistance_star
#check CircuitRecursion.unitaryDistance_conjugation
#print axioms CircuitRecursion.unitaryDistance_conjugation
#check CircuitRecursion.unitaryCommutator_first_error
#print axioms CircuitRecursion.unitaryCommutator_first_error
#check CircuitRecursion.unitaryCommutator_second_error
#print axioms CircuitRecursion.unitaryCommutator_second_error
#check CircuitRecursion.unitaryCommutator_error
#print axioms CircuitRecursion.unitaryCommutator_error
#check CircuitRecursion.active_available
#print axioms CircuitRecursion.active_available
#check CircuitRecursion.stageCircuit_action
#print axioms CircuitRecursion.stageCircuit_action
#check CircuitRecursion.bitOccupation_zero
#print axioms CircuitRecursion.bitOccupation_zero
#check CircuitRecursion.compressionCircuit_action
#print axioms CircuitRecursion.compressionCircuit_action
#check CircuitRecursion.stageCircuit_length
#print axioms CircuitRecursion.stageCircuit_length
#check CircuitRecursion.compressionCircuit_length
#print axioms CircuitRecursion.compressionCircuit_length
#check CircuitRecursion.compressionCircuit_polynomial_bound
#print axioms CircuitRecursion.compressionCircuit_polynomial_bound
#check CircuitRecursion.conjugacyTarget_entries
#print axioms CircuitRecursion.conjugacyTarget_entries
#check CircuitRecursion.conjugacyTarget_scalar
#print axioms CircuitRecursion.conjugacyTarget_scalar
#check CircuitRecursion.intertwinerMass_nonneg
#print axioms CircuitRecursion.intertwinerMass_nonneg
#check CircuitRecursion.intertwinerMass_sum
#print axioms CircuitRecursion.intertwinerMass_sum
#check CircuitRecursion.intertwinerMass_large
#print axioms CircuitRecursion.intertwinerMass_large
#check CircuitRecursion.rationalMaxIndex_error
#print axioms CircuitRecursion.rationalMaxIndex_error
#check CircuitRecursion.conditionedChart_denominator
#print axioms CircuitRecursion.conditionedChart_denominator
#check CircuitRecursion.chartConjugator_action
#print axioms CircuitRecursion.chartConjugator_action
#check CircuitRecursion.dyadicCircuitPrecision_error
#print axioms CircuitRecursion.dyadicCircuitPrecision_error
#check CircuitRecursion.finiteLibrary_extraction_precision
#print axioms CircuitRecursion.finiteLibrary_extraction_precision
#check CircuitRecursion.codeWires_available
#print axioms CircuitRecursion.codeWires_available
#check CircuitRecursion.codeWires_step
#print axioms CircuitRecursion.codeWires_step
#check CircuitRecursion.extendBits_injective
#print axioms CircuitRecursion.extendBits_injective
#check CircuitRecursion.coordinateIsometry_single
#print axioms CircuitRecursion.coordinateIsometry_single
#check CircuitRecursion.run_scalar
#print axioms CircuitRecursion.run_scalar
#check CircuitRecursion.run_zero
#print axioms CircuitRecursion.run_zero
#check CircuitRecursion.encodedBranch_extend
#print axioms CircuitRecursion.encodedBranch_extend
#check CircuitRecursion.shifted_occupation
#print axioms CircuitRecursion.shifted_occupation
#check CircuitRecursion.coordinateIsometry_trans
#print axioms CircuitRecursion.coordinateIsometry_trans
#check CircuitRecursion.extendVector_padding
#print axioms CircuitRecursion.extendVector_padding
#check CircuitRecursion.tailBellCircuit_action
#print axioms CircuitRecursion.tailBellCircuit_action
#check CircuitRecursion.tailBellCircuit_length
#print axioms CircuitRecursion.tailBellCircuit_length
#check CircuitRecursion.register_split
#print axioms CircuitRecursion.register_split
#check CircuitRecursion.extractionCircuit_coherent
#print axioms CircuitRecursion.extractionCircuit_coherent
#check CircuitRecursion.extractionCircuit_purePower
#print axioms CircuitRecursion.extractionCircuit_purePower
#check CircuitRecursion.extractionCircuit_length
#print axioms CircuitRecursion.extractionCircuit_length
#check CircuitRecursion.extractionCircuit_polynomial_bound
#print axioms CircuitRecursion.extractionCircuit_polynomial_bound
#check CircuitRecursion.libraryWireCircuit_value
#print axioms CircuitRecursion.libraryWireCircuit_value
#check CircuitRecursion.libraryWireCircuit_length
#print axioms CircuitRecursion.libraryWireCircuit_length
#check CircuitRecursion.libraryWireCircuit_uses
#print axioms CircuitRecursion.libraryWireCircuit_uses
#check CircuitRecursion.libraryGateCompiler_error
#print axioms CircuitRecursion.libraryGateCompiler_error
#check CircuitRecursion.libraryGateCompiler_length
#print axioms CircuitRecursion.libraryGateCompiler_length
#check CircuitRecursion.libraryGateCompiler_uses
#print axioms CircuitRecursion.libraryGateCompiler_uses
#check CircuitRecursion.finiteLibrary_wordApproximation
#print axioms CircuitRecursion.finiteLibrary_wordApproximation
#check CircuitRecursion.finiteLibrary_extraction_dyadic
#print axioms CircuitRecursion.finiteLibrary_extraction_dyadic
#check CircuitRecursion.instructionWordValue_append
#print axioms CircuitRecursion.instructionWordValue_append
#check CircuitRecursion.instructionWordValue_inverse
#print axioms CircuitRecursion.instructionWordValue_inverse
#check CircuitRecursion.subgroup_instructionWord
#print axioms CircuitRecursion.subgroup_instructionWord
#check CircuitRecursion.dense_instructionWords
#print axioms CircuitRecursion.dense_instructionWords
#check CircuitRecursion.finite_instructionNet
#print axioms CircuitRecursion.finite_instructionNet
#check CircuitRecursion.uniform_instructionLength
#print axioms CircuitRecursion.uniform_instructionLength
#check CircuitRecursion.libraryPrecision_error
#print axioms CircuitRecursion.libraryPrecision_error
#check CircuitRecursion.libraryPrecision_bound
#print axioms CircuitRecursion.libraryPrecision_bound
#check CircuitRecursion.finiteLibrary_extraction
#print axioms CircuitRecursion.finiteLibrary_extraction
#check CircuitRecursion.extractionCircuit_real_bound
#print axioms CircuitRecursion.extractionCircuit_real_bound
#check CircuitRecursion.extractionCircuit_isBigO
#print axioms CircuitRecursion.extractionCircuit_isBigO
#check CircuitRecursion.oracleConst_correct
#print axioms CircuitRecursion.oracleConst_correct
#check CircuitRecursion.oracleMeanPlus_correct
#print axioms CircuitRecursion.oracleMeanPlus_correct
#check CircuitRecursion.oracleMeanMinus_correct
#print axioms CircuitRecursion.oracleMeanMinus_correct
#check CircuitRecursion.halfCosOracle_correct
#print axioms CircuitRecursion.halfCosOracle_correct
#check CircuitRecursion.mergeAngle_bounds
#print axioms CircuitRecursion.mergeAngle_bounds
#check CircuitRecursion.mergeCosOracle_correct
#print axioms CircuitRecursion.mergeCosOracle_correct
#check CircuitRecursion.mergeSinOracle_correct
#print axioms CircuitRecursion.mergeSinOracle_correct
#check CircuitRecursion.halvedMergeCosOracle_correct
#print axioms CircuitRecursion.halvedMergeCosOracle_correct
#check CircuitRecursion.halfSinOracle_correct
#print axioms CircuitRecursion.halfSinOracle_correct
#check CircuitRecursion.halvedMergeSinOracle_correct
#print axioms CircuitRecursion.halvedMergeSinOracle_correct
#check CircuitRecursion.halfCosProgram_eval
#print axioms CircuitRecursion.halfCosProgram_eval
#check CircuitRecursion.halfCosProgram_queries
#print axioms CircuitRecursion.halfCosProgram_queries
#check CircuitRecursion.halfCosProgram_calls
#print axioms CircuitRecursion.halfCosProgram_calls
#check CircuitRecursion.halfAngleDemand_exact
#print axioms CircuitRecursion.halfAngleDemand_exact
#check CircuitRecursion.active_halfAngleDemand_bound
#print axioms CircuitRecursion.active_halfAngleDemand_bound
#check CircuitRecursion.mergeCosProgram_eval
#print axioms CircuitRecursion.mergeCosProgram_eval
#check CircuitRecursion.mergeSinProgram_eval
#print axioms CircuitRecursion.mergeSinProgram_eval
#check CircuitRecursion.mergeCosProgram_resources
#print axioms CircuitRecursion.mergeCosProgram_resources
#check CircuitRecursion.mergeSinProgram_resources
#print axioms CircuitRecursion.mergeSinProgram_resources
#check CircuitRecursion.halfAngleDemand_ge
#print axioms CircuitRecursion.halfAngleDemand_ge
#check CircuitRecursion.mergeCosProgram_precision
#print axioms CircuitRecursion.mergeCosProgram_precision
#check CircuitRecursion.mergeSinProgram_precision
#print axioms CircuitRecursion.mergeSinProgram_precision
#check CircuitRecursion.mergePhaseProgram_correct
#print axioms CircuitRecursion.mergePhaseProgram_correct
#check CircuitRecursion.mergeCosProgram_range
#print axioms CircuitRecursion.mergeCosProgram_range
#check CircuitRecursion.mergeCosProgram_dyadic
#print axioms CircuitRecursion.mergeCosProgram_dyadic
#check CircuitRecursion.mergeSinProgram_dyadic
#print axioms CircuitRecursion.mergeSinProgram_dyadic
#check CircuitRecursion.active_mergePhaseProgram_resources
#print axioms CircuitRecursion.active_mergePhaseProgram_resources
#check CircuitRecursion.bitPurePower_density
#print axioms CircuitRecursion.bitPurePower_density
#check CircuitRecursion.bitPurePower_copywiseInput
#print axioms CircuitRecursion.bitPurePower_copywiseInput
#check CircuitRecursion.readoutCoordinates_physical
#print axioms CircuitRecursion.readoutCoordinates_physical
#check CircuitRecursion.codeEmbedding_mulVec
#print axioms CircuitRecursion.codeEmbedding_mulVec
#check CircuitRecursion.extractionVector_readout
#print axioms CircuitRecursion.extractionVector_readout
#check CircuitRecursion.garbageVector_square
#print axioms CircuitRecursion.garbageVector_square
#check CircuitRecursion.bitPurePower_square
#print axioms CircuitRecursion.bitPurePower_square
#check CircuitRecursion.pureOccupationCoefficients_square
#print axioms CircuitRecursion.pureOccupationCoefficients_square
#check CircuitRecursion.extractionOutput_coherent
#print axioms CircuitRecursion.extractionOutput_coherent
#check CircuitRecursion.extractionOutput_purePower
#print axioms CircuitRecursion.extractionOutput_purePower
#check CircuitRecursion.quaternionMatrix_norm_square
#print axioms CircuitRecursion.quaternionMatrix_norm_square
#check CircuitRecursion.su2_sub_quaternion
#print axioms CircuitRecursion.su2_sub_quaternion
#check CircuitRecursion.su2_distance_coordinates
#print axioms CircuitRecursion.su2_distance_coordinates
#check CircuitRecursion.square_distance_error
#print axioms CircuitRecursion.square_distance_error
#check CircuitRecursion.distanceScore_correct
#print axioms CircuitRecursion.distanceScore_correct
#check CircuitRecursion.fixedNetWord_correct
#print axioms CircuitRecursion.fixedNetWord_correct
#check CircuitRecursion.fixedNetWord_length
#print axioms CircuitRecursion.fixedNetWord_length
#check CircuitRecursion.qubitRepresentative_exists
#print axioms CircuitRecursion.qubitRepresentative_exists
#check CircuitRecursion.qubitRepresentative_spec
#print axioms CircuitRecursion.qubitRepresentative_spec
#check CircuitRecursion.gatePhase_normalized
#print axioms CircuitRecursion.gatePhase_normalized
#check CircuitRecursion.normalizedGate_phase
#print axioms CircuitRecursion.normalizedGate_phase
#check CircuitRecursion.circuitPhase_normalized
#print axioms CircuitRecursion.circuitPhase_normalized
#check CircuitRecursion.normalizedCircuit_phase
#print axioms CircuitRecursion.normalizedCircuit_phase
#check CircuitRecursion.normalized_word_error
#print axioms CircuitRecursion.normalized_word_error
#check CircuitRecursion.normalized_word_uniform_error
#print axioms CircuitRecursion.normalized_word_uniform_error
#check CircuitRecursion.occupationMass_pos_iff
#print axioms CircuitRecursion.occupationMass_pos_iff
#check CircuitRecursion.occupationMass_ge_inverse
#print axioms CircuitRecursion.occupationMass_ge_inverse
#check CircuitRecursion.occupationMass_partial_count
#print axioms CircuitRecursion.occupationMass_partial_count
#check CircuitRecursion.occupationMass_partial_le_one
#print axioms CircuitRecursion.occupationMass_partial_le_one
#check CircuitRecursion.occupationMass_partial_ge_inverse
#print axioms CircuitRecursion.occupationMass_partial_ge_inverse
#check CircuitRecursion.rational_mergeAngle_trig
#print axioms CircuitRecursion.rational_mergeAngle_trig
#check CircuitRecursion.occupation_partial_mergeAngle_trig
#print axioms CircuitRecursion.occupation_partial_mergeAngle_trig
#check CircuitRecursion.oracleAdd_correct
#print axioms CircuitRecursion.oracleAdd_correct
#check CircuitRecursion.oracleNeg_correct
#print axioms CircuitRecursion.oracleNeg_correct
#check CircuitRecursion.dyadic_scale
#print axioms CircuitRecursion.dyadic_scale
#check CircuitRecursion.oracleMul_correct
#print axioms CircuitRecursion.oracleMul_correct
#check CircuitRecursion.oracleInv_correct
#print axioms CircuitRecursion.oracleInv_correct
#check CircuitRecursion.rationalSqrtApprox_correct
#print axioms CircuitRecursion.rationalSqrtApprox_correct
#check CircuitRecursion.sqrt_input_error
#print axioms CircuitRecursion.sqrt_input_error
#check CircuitRecursion.oracleSqrt_correct
#print axioms CircuitRecursion.oracleSqrt_correct
#check CircuitRecursion.rationalSqrtApprox_dyadic
#print axioms CircuitRecursion.rationalSqrtApprox_dyadic
#check CircuitRecursion.rationalSqrtApprox_range
#print axioms CircuitRecursion.rationalSqrtApprox_range
#check CircuitRecursion.castBits_apply
#print axioms CircuitRecursion.castBits_apply
#check CircuitRecursion.pairwiseCoordinates_alice
#print axioms CircuitRecursion.pairwiseCoordinates_alice
#check CircuitRecursion.pairwiseCoordinates_bob
#print axioms CircuitRecursion.pairwiseCoordinates_bob
#check CircuitRecursion.codeWires_eq_original
#print axioms CircuitRecursion.codeWires_eq_original
#check CircuitRecursion.local_register_split
#print axioms CircuitRecursion.local_register_split
#check CircuitRecursion.pairwiseCoordinates_physical
#print axioms CircuitRecursion.pairwiseCoordinates_physical
#check CircuitRecursion.readoutCoordinates_split
#print axioms CircuitRecursion.readoutCoordinates_split
#check CircuitRecursion.boundedWords_mem
#print axioms CircuitRecursion.boundedWords_mem
#check CircuitRecursion.boundedWords_length
#print axioms CircuitRecursion.boundedWords_length
#check CircuitRecursion.precomputedNet_exists
#print axioms CircuitRecursion.precomputedNet_exists
#check CircuitRecursion.numericalBase_exists
#print axioms CircuitRecursion.numericalBase_exists
#check CircuitRecursion.dyadic_numerator_bound
#print axioms CircuitRecursion.dyadic_numerator_bound
#check CircuitRecursion.prefixCircuit_length
#print axioms CircuitRecursion.prefixCircuit_length
#check CircuitRecursion.extendBits_eq_pad
#print axioms CircuitRecursion.extendBits_eq_pad
#check CircuitRecursion.prefixCircuit_eq_lift
#print axioms CircuitRecursion.prefixCircuit_eq_lift
#check CircuitRecursion.extendBits_trans
#print axioms CircuitRecursion.extendBits_trans
#check CircuitRecursion.extendBits_append
#print axioms CircuitRecursion.extendBits_append
#check CircuitRecursion.paddedVector
#print axioms CircuitRecursion.paddedVector
#check CircuitRecursion.prefixCircuit_action
#print axioms CircuitRecursion.prefixCircuit_action
#check CircuitRecursion.compressionCircuit_matrix
#print axioms CircuitRecursion.compressionCircuit_matrix
#check CircuitRecursion.compressionCircuit_coherent
#print axioms CircuitRecursion.compressionCircuit_coherent
#check CircuitRecursion.bitPurePower_expansion
#print axioms CircuitRecursion.bitPurePower_expansion
#check CircuitRecursion.compressionCircuit_purePower
#print axioms CircuitRecursion.compressionCircuit_purePower
#check CircuitRecursion.quaternionCoordinates_bound
#print axioms CircuitRecursion.quaternionCoordinates_bound
#check CircuitRecursion.quaternionCoordinates_mul
#print axioms CircuitRecursion.quaternionCoordinates_mul
#check CircuitRecursion.quaternionSign_abs
#print axioms CircuitRecursion.quaternionSign_abs
#check CircuitRecursion.unit_product_error
#print axioms CircuitRecursion.unit_product_error
#check CircuitRecursion.quaternionProduct_error
#print axioms CircuitRecursion.quaternionProduct_error
#check CircuitRecursion.quaternionProduct_cast
#print axioms CircuitRecursion.quaternionProduct_cast
#check CircuitRecursion.quaternionOracleMul_correct
#print axioms CircuitRecursion.quaternionOracleMul_correct
#check CircuitRecursion.quaternionOracleOne_correct
#print axioms CircuitRecursion.quaternionOracleOne_correct
#check CircuitRecursion.quaternionWordOracle_correct
#print axioms CircuitRecursion.quaternionWordOracle_correct
#check CircuitRecursion.wordOracleQueries_count
#print axioms CircuitRecursion.wordOracleQueries_count
#check CircuitRecursion.wordOracleQueries_precision
#print axioms CircuitRecursion.wordOracleQueries_precision
#check CircuitRecursion.quaternionMatrix_star_mul
#print axioms CircuitRecursion.quaternionMatrix_star_mul
#check CircuitRecursion.quaternionMatrix_det
#print axioms CircuitRecursion.quaternionMatrix_det
#check CircuitRecursion.normalizedQuaternion_val
#print axioms CircuitRecursion.normalizedQuaternion_val
#check CircuitRecursion.normalizedQuaternion_intertwines
#print axioms CircuitRecursion.normalizedQuaternion_intertwines
#check CircuitRecursion.quaternion_difference
#print axioms CircuitRecursion.quaternion_difference
#check CircuitRecursion.su2_intertwiner
#print axioms CircuitRecursion.su2_intertwiner
#check CircuitRecursion.intertwiner_conjugates
#print axioms CircuitRecursion.intertwiner_conjugates
#check CircuitRecursion.unitary_two_phase_special
#print axioms CircuitRecursion.unitary_two_phase_special
#check CircuitRecursion.qubit_phase_special
#print axioms CircuitRecursion.qubit_phase_special
#check CircuitRecursion.rationalMinIndex_le
#print axioms CircuitRecursion.rationalMinIndex_le
#check CircuitRecursion.rationalMinIndex_error
#print axioms CircuitRecursion.rationalMinIndex_error
#check CircuitRecursion.rationalMinIndex_net_error
#print axioms CircuitRecursion.rationalMinIndex_net_error
#check CircuitRecursion.castBits_rfl
#print axioms CircuitRecursion.castBits_rfl
#check CircuitRecursion.castCircuit_rfl
#print axioms CircuitRecursion.castCircuit_rfl
#check CircuitRecursion.castCircuit_length
#print axioms CircuitRecursion.castCircuit_length
#check CircuitRecursion.run_castCircuit
#print axioms CircuitRecursion.run_castCircuit
#check CircuitRecursion.prefix_append
#print axioms CircuitRecursion.prefix_append
#check CircuitRecursion.suffix_append
#print axioms CircuitRecursion.suffix_append
#check CircuitRecursion.single_append
#print axioms CircuitRecursion.single_append
#check CircuitRecursion.run_shift_slice
#print axioms CircuitRecursion.run_shift_slice
#check CircuitRecursion.encodedBranch_apply_append
#print axioms CircuitRecursion.encodedBranch_apply_append
#check CircuitRecursion.discardEffect_bounds
#print axioms CircuitRecursion.discardEffect_bounds
#check CircuitRecursion.discardEffect_pairing
#print axioms CircuitRecursion.discardEffect_pairing
#check CircuitRecursion.extractionOutput_fidelity_one
#print axioms CircuitRecursion.extractionOutput_fidelity_one
#check CircuitRecursion.extractionOutput_robust
#print axioms CircuitRecursion.extractionOutput_robust
#check CircuitRecursion.extractionOutput_robust_up_to_phase
#print axioms CircuitRecursion.extractionOutput_robust_up_to_phase
#check CircuitRecursion.compiledExtraction_error
#print axioms CircuitRecursion.compiledExtraction_error
#check CircuitRecursion.compiledExtraction_fidelity
#print axioms CircuitRecursion.compiledExtraction_fidelity
#check CircuitRecursion.compiledExtraction_length
#print axioms CircuitRecursion.compiledExtraction_length
#check CircuitRecursion.su2AsUnitary_mul
#print axioms CircuitRecursion.su2AsUnitary_mul
#check CircuitRecursion.su2AsUnitary_inv
#print axioms CircuitRecursion.su2AsUnitary_inv
#check CircuitRecursion.balancedFactors_spec
#print axioms CircuitRecursion.balancedFactors_spec
#check CircuitRecursion.skCorrection_value
#print axioms CircuitRecursion.skCorrection_value
#check CircuitRecursion.skCorrection_length
#print axioms CircuitRecursion.skCorrection_length
#check CircuitRecursion.skCorrection_error
#print axioms CircuitRecursion.skCorrection_error
#check CircuitRecursion.skDoubleCorrection_error
#print axioms CircuitRecursion.skDoubleCorrection_error
#check CircuitRecursion.skPairError_zero
#print axioms CircuitRecursion.skPairError_zero
#check CircuitRecursion.skPairError_nonneg
#print axioms CircuitRecursion.skPairError_nonneg
#check CircuitRecursion.skPairError_succ
#print axioms CircuitRecursion.skPairError_succ
#check CircuitRecursion.skPairError_small
#print axioms CircuitRecursion.skPairError_small
#check CircuitRecursion.skPairError_precision
#print axioms CircuitRecursion.skPairError_precision
#check CircuitRecursion.skPairWord_error
#print axioms CircuitRecursion.skPairWord_error
#check CircuitRecursion.skPairWord_length
#print axioms CircuitRecursion.skPairWord_length
#check CircuitRecursion.pow_clog_two_le
#print axioms CircuitRecursion.pow_clog_two_le
#check CircuitRecursion.precisionDepth_length
#print axioms CircuitRecursion.precisionDepth_length
#check CircuitRecursion.su2_synthesis_dyadic
#print axioms CircuitRecursion.su2_synthesis_dyadic
#check CircuitRecursion.su2_inverse_conjugate
#print axioms CircuitRecursion.su2_inverse_conjugate
#check CircuitRecursion.su2_sameScalar_conjugate
#print axioms CircuitRecursion.su2_sameScalar_conjugate
#check CircuitRecursion.su2Conjugate_unitary
#print axioms CircuitRecursion.su2Conjugate_unitary
#check CircuitRecursion.unitaryDistance_conjugate_one
#print axioms CircuitRecursion.unitaryDistance_conjugate_one
#check CircuitRecursion.su2_adjugate
#print axioms CircuitRecursion.su2_adjugate
#check CircuitRecursion.su2_lower_left
#print axioms CircuitRecursion.su2_lower_left
#check CircuitRecursion.su2_lower_right
#print axioms CircuitRecursion.su2_lower_right
#check CircuitRecursion.su2_normalForm
#print axioms CircuitRecursion.su2_normalForm
#check CircuitRecursion.su2_mass
#print axioms CircuitRecursion.su2_mass
#check CircuitRecursion.su2_scalarPart_bounds
#print axioms CircuitRecursion.su2_scalarPart_bounds
#check CircuitRecursion.su2_trace
#print axioms CircuitRecursion.su2_trace
#check CircuitRecursion.su2_add_adjoint
#print axioms CircuitRecursion.su2_add_adjoint
#check CircuitRecursion.su2_distance_square
#print axioms CircuitRecursion.su2_distance_square
#check CircuitRecursion.specialUnitary_isCompact
#print axioms CircuitRecursion.specialUnitary_isCompact
#check CircuitRecursion.specialUnitary_compactSpace
#print axioms CircuitRecursion.specialUnitary_compactSpace
#check CircuitRecursion.su2_uniform_instructionLength
#print axioms CircuitRecursion.su2_uniform_instructionLength
#check CircuitRecursion.matrixReindex_norm
#print axioms CircuitRecursion.matrixReindex_norm
#check CircuitRecursion.singleWire_eq_hom
#print axioms CircuitRecursion.singleWire_eq_hom
#check CircuitRecursion.singleWire_error
#print axioms CircuitRecursion.singleWire_error
#check CircuitRecursion.singleWire_phase
#print axioms CircuitRecursion.singleWire_phase
#check CircuitRecursion.su2ToBool_error
#print axioms CircuitRecursion.su2ToBool_error
#check CircuitRecursion.bellPairYield_feasible
#print axioms CircuitRecursion.bellPairYield_feasible
#check CircuitRecursion.bellPairYield_maximal
#print axioms CircuitRecursion.bellPairYield_maximal
#check CircuitRecursion.bellPairYield_floor_log4
#print axioms CircuitRecursion.bellPairYield_floor_log4
#check CircuitRecursion.log4_eq_half_log2
#print axioms CircuitRecursion.log4_eq_half_log2
#check CircuitRecursion.bellPairYield_floor
#print axioms CircuitRecursion.bellPairYield_floor
#check CircuitRecursion.bellPairYield_cPPT_maximal
#print axioms CircuitRecursion.bellPairYield_cPPT_maximal
#check OperationalCompletion.reservedTargets_subset_pptTargets
#print axioms OperationalCompletion.reservedTargets_subset_pptTargets
#check OperationalCompletion.reservedTargets_lower_bracket
#print axioms OperationalCompletion.reservedTargets_lower_bracket
#check OperationalCompletion.reservedFixedErrorTarget_gaussian
#print axioms OperationalCompletion.reservedFixedErrorTarget_gaussian
#check OperationalCompletion.reservationSafeCutoff_expansion
#print axioms OperationalCompletion.reservationSafeCutoff_expansion
#check OperationalCompletion.reservedProtocol_berryEsseen
#print axioms OperationalCompletion.reservedProtocol_berryEsseen
#check OperationalCompletion.reserved_optimal_gaussian_limit
#print axioms OperationalCompletion.reserved_optimal_gaussian_limit
#check OperationalCompletion.reserved_optimum_gaussian_error
#print axioms OperationalCompletion.reserved_optimum_gaussian_error
#check OperationalCompletion.triangular_reserved_optimum_gaussian_error
#print axioms OperationalCompletion.triangular_reserved_optimum_gaussian_error
#check OperationalCompletion.bellProjector_one
#print axioms OperationalCompletion.bellProjector_one
#check OperationalCompletion.protocol_fidelity_one
#print axioms OperationalCompletion.protocol_fidelity_one
#check OperationalCompletion.density_entropy_rank_bounds
#print axioms OperationalCompletion.density_entropy_rank_bounds
#check OperationalCompletion.capacityRates_nonneg
#print axioms OperationalCompletion.capacityRates_nonneg
#check OperationalCompletion.exactAttainable_zero
#print axioms OperationalCompletion.exactAttainable_zero
#check OperationalCompletion.exactAttainable_subset_faithful
#print axioms OperationalCompletion.exactAttainable_subset_faithful
#check OperationalCompletion.faithfulAttainable_le
#print axioms OperationalCompletion.faithfulAttainable_le
#check OperationalCompletion.exactAttainable_le
#print axioms OperationalCompletion.exactAttainable_le
#check OperationalCompletion.faithfulAttainable_below
#print axioms OperationalCompletion.faithfulAttainable_below
#check OperationalCompletion.exactAttainable_below
#print axioms OperationalCompletion.exactAttainable_below
#check OperationalCompletion.faithfulCapacity_eq
#print axioms OperationalCompletion.faithfulCapacity_eq
#check OperationalCompletion.exactCapacity_eq
#print axioms OperationalCompletion.exactCapacity_eq
#check OperationalCompletion.productLocal_capacities
#print axioms OperationalCompletion.productLocal_capacities
#check OperationalCompletion.cPPT_capacities
#print axioms OperationalCompletion.cPPT_capacities
#check OperationalCompletion.finiteLOCC_capacities
#print axioms OperationalCompletion.finiteLOCC_capacities
#check OperationalCompletion.density_ensemble_integrable
#print axioms OperationalCompletion.density_ensemble_integrable
#check OperationalCompletion.probabilityAverage_density
#print axioms OperationalCompletion.probabilityAverage_density
#check OperationalCompletion.fidelity_probabilityAverage
#print axioms OperationalCompletion.fidelity_probabilityAverage
#check OperationalCompletion.guarantee_le_probabilityAverage
#print axioms OperationalCompletion.guarantee_le_probabilityAverage
#check OperationalCompletion.physical_probability_ensemble_bound
#print axioms OperationalCompletion.physical_probability_ensemble_bound
#check OperationalCompletion.measurable_physical_ensemble_bound
#print axioms OperationalCompletion.measurable_physical_ensemble_bound
#check OperationalCompletion.reservedTotalLoss_nonneg
#print axioms OperationalCompletion.reservedTotalLoss_nonneg
#check OperationalCompletion.reservedProtocol_gaussian_error
#print axioms OperationalCompletion.reservedProtocol_gaussian_error
#check OperationalCompletion.triangular_reserved_gaussian_error
#print axioms OperationalCompletion.triangular_reserved_gaussian_error
#check OperationalCompletion.pureSupportRank_log_le
#print axioms OperationalCompletion.pureSupportRank_log_le
#check OperationalCompletion.reservedTotalLoss_dimension_bound
#print axioms OperationalCompletion.reservedTotalLoss_dimension_bound
#check OperationalCompletion.dimensionScale_sq
#print axioms OperationalCompletion.dimensionScale_sq
#check OperationalCompletion.dimensionScale_tendsto
#print axioms OperationalCompletion.dimensionScale_tendsto
#check OperationalCompletion.sqrt_block_div_dimension_tendsto
#print axioms OperationalCompletion.sqrt_block_div_dimension_tendsto
#check OperationalCompletion.variance_normalization_lower
#print axioms OperationalCompletion.variance_normalization_lower
#check OperationalCompletion.lyapunov_shrinking_bound
#print axioms OperationalCompletion.lyapunov_shrinking_bound
#check OperationalCompletion.shrinking_variance_numerical_conditions
#print axioms OperationalCompletion.shrinking_variance_numerical_conditions
#check OperationalCompletion.triangular_reserved_gaussian_shrinking_variance
#print axioms OperationalCompletion.triangular_reserved_gaussian_shrinking_variance
#check ExtractionLOCC.Tree.leafKraus_complete
#print axioms ExtractionLOCC.Tree.leafKraus_complete
#check ExtractionLOCC.Tree.channel_completelyPositive
#print axioms ExtractionLOCC.Tree.channel_completelyPositive
#check ExtractionLOCC.Tree.channel_tracePreserving
#print axioms ExtractionLOCC.Tree.channel_tracePreserving
#check ExtractionLOCC.Tree.channel_done
#print axioms ExtractionLOCC.Tree.channel_done
#check ExtractionLOCC.Tree.channel_alice
#print axioms ExtractionLOCC.Tree.channel_alice
#check ExtractionLOCC.Tree.channel_bob
#print axioms ExtractionLOCC.Tree.channel_bob
#check ExtractionLOCC.Tree.pt_identity
#print axioms ExtractionLOCC.Tree.pt_identity
#check ExtractionLOCC.Tree.channel_pt_completelyPositive
#print axioms ExtractionLOCC.Tree.channel_pt_completelyPositive
#check ExtractionLOCC.Tree.ptLeafKraus_complete
#print axioms ExtractionLOCC.Tree.ptLeafKraus_complete
#check ExtractionLOCC.Tree.product_channel
#print axioms ExtractionLOCC.Tree.product_channel
#check ExtractionLOCC.Tree.protocol_apply
#print axioms ExtractionLOCC.Tree.protocol_apply
#check ExtractionLOCC.IsFiniteLOCC.completelyPositive
#print axioms ExtractionLOCC.IsFiniteLOCC.completelyPositive
#check ExtractionLOCC.IsFiniteLOCC.tracePreserving
#print axioms ExtractionLOCC.IsFiniteLOCC.tracePreserving
#check ExtractionLOCC.IsFiniteLOCC.pt_completelyPositive
#print axioms ExtractionLOCC.IsFiniteLOCC.pt_completelyPositive
#check ExtractionLOCC.tree_isFiniteLOCCProtocol
#print axioms ExtractionLOCC.tree_isFiniteLOCCProtocol
#check ExtractionLOCC.productLocal_isFiniteLOCCProtocol
#print axioms ExtractionLOCC.productLocal_isFiniteLOCCProtocol
#check ExtractionLOCC.IsFiniteLOCC.exists_actual_protocol
#print axioms ExtractionLOCC.IsFiniteLOCC.exists_actual_protocol
#check ExtractionLOCC.choi_injective
#print axioms ExtractionLOCC.choi_injective
#check ExtractionLOCC.continuous_evaluation
#print axioms ExtractionLOCC.continuous_evaluation
#check ExtractionLOCC.isClosed_completelyPositive
#print axioms ExtractionLOCC.isClosed_completelyPositive
#check ExtractionLOCC.isClosed_tracePreserving
#print axioms ExtractionLOCC.isClosed_tracePreserving
#check ExtractionLOCC.choi_ptConjugate
#print axioms ExtractionLOCC.choi_ptConjugate
#check ExtractionLOCC.continuous_choi_ptConjugate
#print axioms ExtractionLOCC.continuous_choi_ptConjugate
#check ExtractionLOCC.isClosed_pt_completelyPositive
#print axioms ExtractionLOCC.isClosed_pt_completelyPositive
#check ExtractionLOCC.IsFiniteLOCC.isClosureLOCC
#print axioms ExtractionLOCC.IsFiniteLOCC.isClosureLOCC
#check ExtractionLOCC.IsClosureLOCC.completelyPositive
#print axioms ExtractionLOCC.IsClosureLOCC.completelyPositive
#check ExtractionLOCC.IsClosureLOCC.tracePreserving
#print axioms ExtractionLOCC.IsClosureLOCC.tracePreserving
#check ExtractionLOCC.IsClosureLOCC.pt_completelyPositive
#print axioms ExtractionLOCC.IsClosureLOCC.pt_completelyPositive
#check ExtractionLOCC.finiteLOCC_isClosureLOCCProtocol
#print axioms ExtractionLOCC.finiteLOCC_isClosureLOCCProtocol
#check ExtractionLOCC.productLocal_isClosureLOCCProtocol
#print axioms ExtractionLOCC.productLocal_isClosureLOCCProtocol
#check ExtractionLOCC.IsClosureLOCC.exists_actual_protocol
#print axioms ExtractionLOCC.IsClosureLOCC.exists_actual_protocol
#check ExtractionLOCC.Instrument.outcome_completelyPositive
#print axioms ExtractionLOCC.Instrument.outcome_completelyPositive
#check ExtractionLOCC.Instrument.ofCP_outcomeMap
#print axioms ExtractionLOCC.Instrument.ofCP_outcomeMap
#check ExtractionLOCC.Tree.channel_aliceInstrument
#print axioms ExtractionLOCC.Tree.channel_aliceInstrument
#check ExtractionLOCC.Tree.channel_bobInstrument
#print axioms ExtractionLOCC.Tree.channel_bobInstrument
#check ExtractionRains.choi_measurePrepare
#print axioms ExtractionRains.choi_measurePrepare
#check ExtractionRains.measurePrepare_completelyPositive
#print axioms ExtractionRains.measurePrepare_completelyPositive
#check ExtractionRains.failureState_posSemidef
#print axioms ExtractionRains.failureState_posSemidef
#check ExtractionRains.failureState_trace
#print axioms ExtractionRains.failureState_trace
#check ExtractionRains.channel_completelyPositive
#print axioms ExtractionRains.channel_completelyPositive
#check ExtractionRains.channel_tracePreserving
#print axioms ExtractionRains.channel_tracePreserving
#check ExtractionRains.bell_failureState_trace
#print axioms ExtractionRains.bell_failureState_trace
#check ExtractionRains.channel_target_overlap
#print axioms ExtractionRains.channel_target_overlap
#check ExtractionRains.plusProjection_posSemidef
#print axioms ExtractionRains.plusProjection_posSemidef
#check ExtractionRains.minusProjection_posSemidef
#print axioms ExtractionRains.minusProjection_posSemidef
#check ExtractionRains.plusEffect_posSemidef
#print axioms ExtractionRains.plusEffect_posSemidef
#check ExtractionRains.minusEffect_posSemidef
#print axioms ExtractionRains.minusEffect_posSemidef
#check ExtractionRains.pt_channel_formula
#print axioms ExtractionRains.pt_channel_formula
#check ExtractionRains.pt_channel_decomposition
#print axioms ExtractionRains.pt_channel_decomposition
#check ExtractionRains.channel_pt_completelyPositive
#print axioms ExtractionRains.channel_pt_completelyPositive
#check ExtractionRains.protocol_apply
#print axioms ExtractionRains.protocol_apply
#check ExtractionRains.protocol_targetEffect
#print axioms ExtractionRains.protocol_targetEffect
#check ExtractionRains.protocol_fidelity
#print axioms ExtractionRains.protocol_fidelity
#check ExtractionRains.rainsEffect_exists_actual_protocol
#print axioms ExtractionRains.rainsEffect_exists_actual_protocol
#check ExtractionRains.rainsEffect_iff_actual_protocol_effect
#print axioms ExtractionRains.rainsEffect_iff_actual_protocol_effect
#check ExtractionSchur.errorRankBudgetMaximum_attained
#print axioms ExtractionSchur.errorRankBudgetMaximum_attained
#check ExtractionSchur.errorRankBudgetMaximum_full_rank
#print axioms ExtractionSchur.errorRankBudgetMaximum_full_rank
#check ExtractionSchur.errorRankBudgetMaximum_isGreatest
#print axioms ExtractionSchur.errorRankBudgetMaximum_isGreatest
#check ExtractionSchur.errorRankBudgetMaximum_log_limit
#print axioms ExtractionSchur.errorRankBudgetMaximum_log_limit
#check ExtractionSchur.exactRankBudgetMaximum_attained
#print axioms ExtractionSchur.exactRankBudgetMaximum_attained
#check ExtractionSchur.exactRankBudgetMaximum_bounds
#print axioms ExtractionSchur.exactRankBudgetMaximum_bounds
#check ExtractionSchur.exactRankBudgetMaximum_eventually_local
#print axioms ExtractionSchur.exactRankBudgetMaximum_eventually_local
#check ExtractionSchur.exactRankBudgetMaximum_full_rank
#print axioms ExtractionSchur.exactRankBudgetMaximum_full_rank
#check ExtractionSchur.exactRankBudgetMaximum_log_correction_limit
#print axioms ExtractionSchur.exactRankBudgetMaximum_log_correction_limit
#check ExtractionSchur.exact_fixedOrbit_physical_budget
#print axioms ExtractionSchur.exact_fixedOrbit_physical_budget
#check ExtractionSchur.flatOrbitErrorMaximum_attained
#print axioms ExtractionSchur.flatOrbitErrorMaximum_attained
#check ExtractionSchur.flatOrbitErrorMaximum_bounds
#print axioms ExtractionSchur.flatOrbitErrorMaximum_bounds
#check ExtractionSchur.flatOrbitErrorMaximum_full_rank
#print axioms ExtractionSchur.flatOrbitErrorMaximum_full_rank
#check ExtractionSchur.flatOrbitErrorMaximum_isGreatest
#print axioms ExtractionSchur.flatOrbitErrorMaximum_isGreatest
#check ExtractionSchur.flatOrbitErrorMaximum_log_limit
#print axioms ExtractionSchur.flatOrbitErrorMaximum_log_limit
#check ExtractionSchur.flatOrbit_full_rank_minimax
#print axioms ExtractionSchur.flatOrbit_full_rank_minimax
#check ExtractionSchur.flatOrbit_minimax_profile_bounds
#print axioms ExtractionSchur.flatOrbit_minimax_profile_bounds
#check ExtractionSchur.flatOrbit_target_uniform_minimax
#print axioms ExtractionSchur.flatOrbit_target_uniform_minimax
#check ExtractionSchur.flatOrbit_target_uniform_relative_error
#print axioms ExtractionSchur.flatOrbit_target_uniform_relative_error
#check ExtractionSchur.orbitExactMaximum_attained
#print axioms ExtractionSchur.orbitExactMaximum_attained
#check ExtractionSchur.orbitExactMaximum_bounds
#print axioms ExtractionSchur.orbitExactMaximum_bounds
#check ExtractionSchur.orbitExactMaximum_eventually_local
#print axioms ExtractionSchur.orbitExactMaximum_eventually_local
#check ExtractionSchur.orbitExactMaximum_full_rank
#print axioms ExtractionSchur.orbitExactMaximum_full_rank
#check ExtractionSchur.orbitExactMaximum_isGreatest
#print axioms ExtractionSchur.orbitExactMaximum_isGreatest
#check ExtractionSchur.orbitExactMaximum_log_correction_limit
#print axioms ExtractionSchur.orbitExactMaximum_log_correction_limit
#check ExtractionSchur.rankBudgetEta_limit
#print axioms ExtractionSchur.rankBudgetEta_limit
#check ExtractionSchur.rankBudgetPacking_ratio_limit
#print axioms ExtractionSchur.rankBudgetPacking_ratio_limit
#check ExtractionSchur.rankBudget_class_minimax_finite
#print axioms ExtractionSchur.rankBudget_class_minimax_finite
#check ExtractionSchur.rankBudget_completelyPPT_eq_minimaxValue
#print axioms ExtractionSchur.rankBudget_completelyPPT_eq_minimaxValue
#check ExtractionSchur.rankBudget_full_rank_minimax
#print axioms ExtractionSchur.rankBudget_full_rank_minimax
#check ExtractionSchur.rankBudget_physical_class_chain
#print axioms ExtractionSchur.rankBudget_physical_class_chain
#check ExtractionSchur.rankBudget_physical_relative_bound
#print axioms ExtractionSchur.rankBudget_physical_relative_bound
#check ExtractionSchur.rankBudget_target_uniform_minimax
#print axioms ExtractionSchur.rankBudget_target_uniform_minimax
#check ExtractionSchur.rankBudget_target_uniform_relative_error
#print axioms ExtractionSchur.rankBudget_target_uniform_relative_error
#check ExtractionAPPT.trace_cfc
#print axioms ExtractionAPPT.trace_cfc
#check ExtractionAPPT.quantumEntropy_eq_spectral
#print axioms ExtractionAPPT.quantumEntropy_eq_spectral
#check ExtractionAPPT.continuousOn_quantumEntropy
#print axioms ExtractionAPPT.continuousOn_quantumEntropy
#check ExtractionAPPT.cfc_submatrix
#print axioms ExtractionAPPT.cfc_submatrix
#check ExtractionAPPT.quantumEntropy_submatrix
#print axioms ExtractionAPPT.quantumEntropy_submatrix
#check ExtractionAPPT.flatten_density
#print axioms ExtractionAPPT.flatten_density
#check ExtractionAPPT.flatten_entropy
#print axioms ExtractionAPPT.flatten_entropy
#check ExtractionAPPT.flatten_spectral_entropy
#print axioms ExtractionAPPT.flatten_spectral_entropy
#check ExtractionAPPT.continuousOn_appt_entropy
#print axioms ExtractionAPPT.continuousOn_appt_entropy
#check ExtractionAPPT.exists_appt_entropy_isLeast
#print axioms ExtractionAPPT.exists_appt_entropy_isLeast
#check ExtractionAPPT.exists_appt_entropy_eq_inf
#print axioms ExtractionAPPT.exists_appt_entropy_eq_inf
#check ExtractionAPPT.physicalCapacity_eq
#print axioms ExtractionAPPT.physicalCapacity_eq
#check ExtractionAPPT.physicalCapacity_eq_cPPT
#print axioms ExtractionAPPT.physicalCapacity_eq_cPPT
#check ExtractionAPPT.exists_appt_capacity_isGreatest
#print axioms ExtractionAPPT.exists_appt_capacity_isGreatest
#check ExtractionAPPT.exists_appt_capacity_eq_sup
#print axioms ExtractionAPPT.exists_appt_capacity_eq_sup
#check ExtractionAPPT.apptMaxCapacity_eq
#print axioms ExtractionAPPT.apptMaxCapacity_eq
#check ExtractionAPPT.exists_appt_purity_maximizer
#print axioms ExtractionAPPT.exists_appt_purity_maximizer
#check ExtractionAPPT.entropy_ge_neg_log_collision
#print axioms ExtractionAPPT.entropy_ge_neg_log_collision
#check ExtractionAPPT.density_entropy_purity_bound
#print axioms ExtractionAPPT.density_entropy_purity_bound
#check ExtractionAPPT.physicalCapacity_le_purity
#print axioms ExtractionAPPT.physicalCapacity_le_purity
#check ExtractionAPPT.apptMaxCapacity_le_puritySup
#print axioms ExtractionAPPT.apptMaxCapacity_le_puritySup
#check ExtractionAPPT.physicalCapacity_eq_closureLOCC
#print axioms ExtractionAPPT.physicalCapacity_eq_closureLOCC
#check ExtractionAPPT.schmidt_product_le_half
#print axioms ExtractionAPPT.schmidt_product_le_half
#check ExtractionAPPT.schmidtSigned_lower
#print axioms ExtractionAPPT.schmidtSigned_lower
#check ExtractionAPPT.pure_partialTranspose_lower
#print axioms ExtractionAPPT.pure_partialTranspose_lower
#check ExtractionAPPT.spikeState_density
#print axioms ExtractionAPPT.spikeState_density
#check ExtractionAPPT.spikeState_absolutelyPPT
#print axioms ExtractionAPPT.spikeState_absolutelyPPT
#check ExtractionAPPT.spikeState_mem_appt
#print axioms ExtractionAPPT.spikeState_mem_appt
#check ExtractionAPPT.projection_spectrum_zero_one
#print axioms ExtractionAPPT.projection_spectrum_zero_one
#check ExtractionAPPT.cfc_affine_projection
#print axioms ExtractionAPPT.cfc_affine_projection
#check ExtractionAPPT.quantumEntropy_affine_rankOne
#print axioms ExtractionAPPT.quantumEntropy_affine_rankOne
#check ExtractionAPPT.spikeState_entropy
#print axioms ExtractionAPPT.spikeState_entropy
#check ExtractionAPPT.spikeState_capacity
#print axioms ExtractionAPPT.spikeState_capacity
#check ExtractionAPPT.spike_capacity_le_apptMax
#print axioms ExtractionAPPT.spike_capacity_le_apptMax
#check ExtractionAPPT.spike_rate_error_bounds
#print axioms ExtractionAPPT.spike_rate_error_bounds
#check ExtractionAPPT.spikeState_capacity_error_bounds
#print axioms ExtractionAPPT.spikeState_capacity_error_bounds
#check ExtractionAPPT.spike_capacity_coefficient_limit
#print axioms ExtractionAPPT.spike_capacity_coefficient_limit
#check ExtractionAPPT.normalized_log_budget_limit
#print axioms ExtractionAPPT.normalized_log_budget_limit
#check ExtractionAPPT.balanced_purity_excess_limit
#print axioms ExtractionAPPT.balanced_purity_excess_limit
#check ExtractionAPPT.balanced_purity_capacity_budget_limit
#print axioms ExtractionAPPT.balanced_purity_capacity_budget_limit
#check ExtractionAPPT.balanced_apptMaxCapacity_upper
#print axioms ExtractionAPPT.balanced_apptMaxCapacity_upper
#check ExtractionAPPT.balanced_apptMaxCapacity_upper_remainder
#print axioms ExtractionAPPT.balanced_apptMaxCapacity_upper_remainder
#check ExtractionAPPT.spikeState_scaled_capacity_limit
#print axioms ExtractionAPPT.spikeState_scaled_capacity_limit
#check ExtractionAPPT.balanced_apptMaxCapacity_lower
#print axioms ExtractionAPPT.balanced_apptMaxCapacity_lower
#check ExtractionAPPT.balanced_apptMaxCapacity_first_order_bounds
#print axioms ExtractionAPPT.balanced_apptMaxCapacity_first_order_bounds
#check OperationalCompletion.heterogeneous_projection_protocol
#print axioms OperationalCompletion.heterogeneous_projection_protocol
#check SpectralProtocol.oneShotSpectralEnvelope_actual_lower
#print axioms SpectralProtocol.oneShotSpectralEnvelope_actual_lower
#check SpectralProtocol.oneShotSpectralEnvelope_actual_upper
#print axioms SpectralProtocol.oneShotSpectralEnvelope_actual_upper
#check MinimaxProfile.tensorProjection_rank_le
#print axioms MinimaxProfile.tensorProjection_rank_le
#check MinimaxProfile.tensorProjection_mass_ge
#print axioms MinimaxProfile.tensorProjection_mass_ge
#check ExtractionSchur.haarOrbitAverage_range
#print axioms ExtractionSchur.haarOrbitAverage_range
#check ExtractionSchur.haarOrbitAverage_rank
#print axioms ExtractionSchur.haarOrbitAverage_rank
#check ExtractionSchur.haarOrbitAverage_trace_square
#print axioms ExtractionSchur.haarOrbitAverage_trace_square
#check ExtractionSchur.haarMinorMoment_product
#print axioms ExtractionSchur.haarMinorMoment_product
#check ExtractionCP.amplification
#print axioms ExtractionCP.amplification
#check ExtractionCP.CompletelyPositive
#print axioms ExtractionCP.CompletelyPositive
#check ExtractionCP.TracePreserving
#print axioms ExtractionCP.TracePreserving
#check ExtractionCP.choi
#print axioms ExtractionCP.choi
#check ExtractionCP.choiKraus
#print axioms ExtractionCP.choiKraus
#check ExtractionCP.ptConjugate
#print axioms ExtractionCP.ptConjugate
#check ExtractionCP.PPTChannel
#print axioms ExtractionCP.PPTChannel
#check ExtractionCP.PPTChannel.toKrausPPTProtocol
#print axioms ExtractionCP.PPTChannel.toKrausPPTProtocol
#check ExtractionCP.ofKrausPPTProtocol
#print axioms ExtractionCP.ofKrausPPTProtocol
#check OperationalCompletion.reservedProtocol
#print axioms OperationalCompletion.reservedProtocol
#check OperationalCompletion.reservationLocal
#print axioms OperationalCompletion.reservationLocal
#check OperationalCompletion.reservationMainLocal
#print axioms OperationalCompletion.reservationMainLocal
#check OperationalCompletion.paperReservationDivisor
#print axioms OperationalCompletion.paperReservationDivisor
#check OperationalCompletion.paperReservedPacking
#print axioms OperationalCompletion.paperReservedPacking
#check OperationalCompletion.reservationLoss
#print axioms OperationalCompletion.reservationLoss
#check OperationalCompletion.reservationSafeCutoff
#print axioms OperationalCompletion.reservationSafeCutoff
#check OperationalCompletion.balancedReservationPacking
#print axioms OperationalCompletion.balancedReservationPacking
#check OperationalCompletion.balancedReservedWidth
#print axioms OperationalCompletion.balancedReservedWidth
#check OperationalCompletion.fidelityExponent
#print axioms OperationalCompletion.fidelityExponent
#check OperationalCompletion.protocolOptimum
#print axioms OperationalCompletion.protocolOptimum
#check ExtractionDeviation.berryEsseenConstant
#print axioms ExtractionDeviation.berryEsseenConstant
#check ExtractionDeviation.informationBerryEsseenError
#print axioms ExtractionDeviation.informationBerryEsseenError
#check ExtractionDeviation.compressionLoss
#print axioms ExtractionDeviation.compressionLoss
#check ExtractionDeviation.finiteCappedTarget
#print axioms ExtractionDeviation.finiteCappedTarget
#check ExtractionDeviation.pptTargets
#print axioms ExtractionDeviation.pptTargets
#check ExtractionDeviation.universalTargets
#print axioms ExtractionDeviation.universalTargets
#check ExtractionDeviation.pptFixedErrorTarget
#print axioms ExtractionDeviation.pptFixedErrorTarget
#check ExtractionDeviation.universalFixedErrorTarget
#print axioms ExtractionDeviation.universalFixedErrorTarget
#check ExtractionDeviation.dimensionLossBound
#print axioms ExtractionDeviation.dimensionLossBound
#check ExtractionSchur.projectedGram
#print axioms ExtractionSchur.projectedGram
#check ExtractionSchur.projectionOverlap
#print axioms ExtractionSchur.projectionOverlap
#check ExtractionSchur.haarOverlapMoment
#print axioms ExtractionSchur.haarOverlapMoment
#check ExtractionSchur.compressionLinear
#print axioms ExtractionSchur.compressionLinear
#check ExtractionSchur.haarTwirlLinear
#print axioms ExtractionSchur.haarTwirlLinear
#check ExtractionSchur.cyclicTensorMean
#print axioms ExtractionSchur.cyclicTensorMean
#check ExtractionSchur.HasDescendingSubsequence
#print axioms ExtractionSchur.HasDescendingSubsequence
#check ExtractionSchur.DescendingAvoider
#print axioms ExtractionSchur.DescendingAvoider
#check ExtractionSchur.descendingAvoiderCount
#print axioms ExtractionSchur.descendingAvoiderCount
#check CircuitRecursion.compressionCircuit
#print axioms CircuitRecursion.compressionCircuit
#check CircuitRecursion.bitPurePower
#print axioms CircuitRecursion.bitPurePower
#check CircuitRecursion.bellPairYield
#print axioms CircuitRecursion.bellPairYield
#check CircuitRecursion.extractionCircuit
#print axioms CircuitRecursion.extractionCircuit
#check CircuitRecursion.extractionOutput
#print axioms CircuitRecursion.extractionOutput
#check CircuitRecursion.approximateExtractionOutput
#print axioms CircuitRecursion.approximateExtractionOutput
#check CircuitRecursion.physicalLocalReadoutCoordinates
#print axioms CircuitRecursion.physicalLocalReadoutCoordinates
#check CircuitRecursion.readoutCoordinates
#print axioms CircuitRecursion.readoutCoordinates
#check CircuitRecursion.localReadoutCoordinates
#print axioms CircuitRecursion.localReadoutCoordinates
#check CircuitRecursion.codePairCoordinates
#print axioms CircuitRecursion.codePairCoordinates
#check CircuitRecursion.usesFiniteLibrary
#print axioms CircuitRecursion.usesFiniteLibrary
#check CircuitRecursion.instructionWordValue
#print axioms CircuitRecursion.instructionWordValue
#check CircuitRecursion.skPairWord
#print axioms CircuitRecursion.skPairWord
#check CircuitRecursion.libraryGateCompiler
#print axioms CircuitRecursion.libraryGateCompiler
#check CircuitRecursion.libraryPrecision
#print axioms CircuitRecursion.libraryPrecision
#check CircuitRecursion.circuitPhase
#print axioms CircuitRecursion.circuitPhase
#check CircuitRecursion.conjugacyFrame
#print axioms CircuitRecursion.conjugacyFrame
#check CircuitRecursion.conjugacyTarget
#print axioms CircuitRecursion.conjugacyTarget
#check CircuitRecursion.intertwinerMass
#print axioms CircuitRecursion.intertwinerMass
#check CircuitRecursion.rationalMaxIndex
#print axioms CircuitRecursion.rationalMaxIndex
#check CircuitRecursion.chartConjugator
#print axioms CircuitRecursion.chartConjugator
#check CircuitRecursion.RationalOracle
#print axioms CircuitRecursion.RationalOracle
#check CircuitRecursion.Approximates
#print axioms CircuitRecursion.Approximates
#check CircuitRecursion.oracleAdd
#print axioms CircuitRecursion.oracleAdd
#check CircuitRecursion.oracleNeg
#print axioms CircuitRecursion.oracleNeg
#check CircuitRecursion.oracleMul
#print axioms CircuitRecursion.oracleMul
#check CircuitRecursion.oracleInv
#print axioms CircuitRecursion.oracleInv
#check CircuitRecursion.rationalSqrtApprox
#print axioms CircuitRecursion.rationalSqrtApprox
#check CircuitRecursion.oracleSqrt
#print axioms CircuitRecursion.oracleSqrt
#check CircuitRecursion.oracleConst
#print axioms CircuitRecursion.oracleConst
#check CircuitRecursion.oracleMeanPlus
#print axioms CircuitRecursion.oracleMeanPlus
#check CircuitRecursion.oracleMeanMinus
#print axioms CircuitRecursion.oracleMeanMinus
#check CircuitRecursion.halfCosOracle
#print axioms CircuitRecursion.halfCosOracle
#check CircuitRecursion.mergeCosOracle
#print axioms CircuitRecursion.mergeCosOracle
#check CircuitRecursion.mergeSinOracle
#print axioms CircuitRecursion.mergeSinOracle
#check CircuitRecursion.halfSinOracle
#print axioms CircuitRecursion.halfSinOracle
#check CircuitRecursion.ScalarProgram
#print axioms CircuitRecursion.ScalarProgram
#check CircuitRecursion.ScalarProgram.eval
#print axioms CircuitRecursion.ScalarProgram.eval
#check CircuitRecursion.ScalarProgram.queries
#print axioms CircuitRecursion.ScalarProgram.queries
#check CircuitRecursion.ScalarProgram.sqrtCalls
#print axioms CircuitRecursion.ScalarProgram.sqrtCalls
#check CircuitRecursion.ScalarProgram.rationalCalls
#print axioms CircuitRecursion.ScalarProgram.rationalCalls
#check CircuitRecursion.halfCosProgram
#print axioms CircuitRecursion.halfCosProgram
#check CircuitRecursion.halfAngleDemand
#print axioms CircuitRecursion.halfAngleDemand
#check CircuitRecursion.mergeCosProgram
#print axioms CircuitRecursion.mergeCosProgram
#check CircuitRecursion.mergeSinProgram
#print axioms CircuitRecursion.mergeSinProgram
#check CircuitRecursion.ScalarProgram.maxRootPrecision
#print axioms CircuitRecursion.ScalarProgram.maxRootPrecision
#check CircuitRecursion.quaternionCoordinates
#print axioms CircuitRecursion.quaternionCoordinates
#check CircuitRecursion.quaternionRight
#print axioms CircuitRecursion.quaternionRight
#check CircuitRecursion.quaternionSign
#print axioms CircuitRecursion.quaternionSign
#check CircuitRecursion.quaternionProduct
#print axioms CircuitRecursion.quaternionProduct
#check CircuitRecursion.QuaternionOracle
#print axioms CircuitRecursion.QuaternionOracle
#check CircuitRecursion.QApproximates
#print axioms CircuitRecursion.QApproximates
#check CircuitRecursion.quaternionOracleMul
#print axioms CircuitRecursion.quaternionOracleMul
#check CircuitRecursion.quaternionOracleOne
#print axioms CircuitRecursion.quaternionOracleOne
#check CircuitRecursion.quaternionWordOracle
#print axioms CircuitRecursion.quaternionWordOracle
#check CircuitRecursion.wordOracleQueries
#print axioms CircuitRecursion.wordOracleQueries
#check CircuitRecursion.rationalSquaredDistance
#print axioms CircuitRecursion.rationalSquaredDistance
#check CircuitRecursion.distanceScore
#print axioms CircuitRecursion.distanceScore
#check CircuitRecursion.fixedNetWord
#print axioms CircuitRecursion.fixedNetWord
#check CircuitRecursion.boundedWords
#print axioms CircuitRecursion.boundedWords
#check CircuitRecursion.DyadicQuaternionOracle
#print axioms CircuitRecursion.DyadicQuaternionOracle
#check CircuitRecursion.dyadicQuaternionOracle
#print axioms CircuitRecursion.dyadicQuaternionOracle
#check CircuitRecursion.DyadicQApproximates
#print axioms CircuitRecursion.DyadicQApproximates
#check OperationalCompletion.reservedTargets
#print axioms OperationalCompletion.reservedTargets
#check OperationalCompletion.reservedFixedErrorTarget
#print axioms OperationalCompletion.reservedFixedErrorTarget
#check OperationalCompletion.reservedTotalLoss
#print axioms OperationalCompletion.reservedTotalLoss
#check OperationalCompletion.faithfulAttainableRates
#print axioms OperationalCompletion.faithfulAttainableRates
#check OperationalCompletion.exactAttainableRates
#print axioms OperationalCompletion.exactAttainableRates
#check OperationalCompletion.faithfulCapacity
#print axioms OperationalCompletion.faithfulCapacity
#check OperationalCompletion.exactCapacity
#print axioms OperationalCompletion.exactCapacity
#check OperationalCompletion.protocolFidelityLinear
#print axioms OperationalCompletion.protocolFidelityLinear
#check OperationalCompletion.matrixTraceLinear
#print axioms OperationalCompletion.matrixTraceLinear
#check OperationalCompletion.probabilityAverage
#print axioms OperationalCompletion.probabilityAverage
#check OperationalCompletion.dimensionScale
#print axioms OperationalCompletion.dimensionScale
#check ExtractionLOCC.Tree
#print axioms ExtractionLOCC.Tree
#check ExtractionLOCC.Tree.Leaf
#print axioms ExtractionLOCC.Tree.Leaf
#check ExtractionLOCC.Tree.leafAlice
#print axioms ExtractionLOCC.Tree.leafAlice
#check ExtractionLOCC.Tree.leafBob
#print axioms ExtractionLOCC.Tree.leafBob
#check ExtractionLOCC.Tree.leafKraus
#print axioms ExtractionLOCC.Tree.leafKraus
#check ExtractionLOCC.Tree.channel
#print axioms ExtractionLOCC.Tree.channel
#check ExtractionLOCC.Tree.ptLeafKraus
#print axioms ExtractionLOCC.Tree.ptLeafKraus
#check ExtractionLOCC.Tree.product
#print axioms ExtractionLOCC.Tree.product
#check ExtractionLOCC.Tree.pptChannel
#print axioms ExtractionLOCC.Tree.pptChannel
#check ExtractionLOCC.Tree.protocol
#print axioms ExtractionLOCC.Tree.protocol
#check ExtractionLOCC.IsFiniteLOCC
#print axioms ExtractionLOCC.IsFiniteLOCC
#check ExtractionLOCC.IsFiniteLOCCProtocol
#print axioms ExtractionLOCC.IsFiniteLOCCProtocol
#check ExtractionLOCC.Instrument
#print axioms ExtractionLOCC.Instrument
#check ExtractionLOCC.Instrument.ofCP
#print axioms ExtractionLOCC.Instrument.ofCP
#check ExtractionLOCC.Instrument.outcomeMap
#print axioms ExtractionLOCC.Instrument.outcomeMap
#check ExtractionLOCC.Tree.aliceInstrument
#print axioms ExtractionLOCC.Tree.aliceInstrument
#check ExtractionLOCC.Tree.bobInstrument
#print axioms ExtractionLOCC.Tree.bobInstrument
#check ExtractionLOCC.coefficientTopology
#print axioms ExtractionLOCC.coefficientTopology
#check ExtractionLOCC.IsClosureLOCC
#print axioms ExtractionLOCC.IsClosureLOCC
#check ExtractionLOCC.IsClosureLOCCProtocol
#print axioms ExtractionLOCC.IsClosureLOCCProtocol
#check ExtractionRains.measurePrepare
#print axioms ExtractionRains.measurePrepare
#check ExtractionRains.failureState
#print axioms ExtractionRains.failureState
#check ExtractionRains.channel
#print axioms ExtractionRains.channel
#check ExtractionRains.plusProjection
#print axioms ExtractionRains.plusProjection
#check ExtractionRains.minusProjection
#print axioms ExtractionRains.minusProjection
#check ExtractionRains.plusEffect
#print axioms ExtractionRains.plusEffect
#check ExtractionRains.minusEffect
#print axioms ExtractionRains.minusEffect
#check ExtractionRains.pptChannel
#print axioms ExtractionRains.pptChannel
#check ExtractionRains.protocol
#print axioms ExtractionRains.protocol
#check ExtractionSchur.RankBudgetInput
#print axioms ExtractionSchur.RankBudgetInput
#check ExtractionSchur.rankBudgetClassMinimax
#print axioms ExtractionSchur.rankBudgetClassMinimax
#check ExtractionSchur.rankBudgetProjection
#print axioms ExtractionSchur.rankBudgetProjection
#check ExtractionSchur.physicalHaarAverage
#print axioms ExtractionSchur.physicalHaarAverage
#check ExtractionSchur.rankBudgetOrbitInput
#print axioms ExtractionSchur.rankBudgetOrbitInput
#check ExtractionSchur.RankProtocolClass
#print axioms ExtractionSchur.RankProtocolClass
#check ExtractionSchur.RankProtocolClass.Allows
#print axioms ExtractionSchur.RankProtocolClass.Allows
#check ExtractionSchur.rankBudgetPhysicalMinimax
#print axioms ExtractionSchur.rankBudgetPhysicalMinimax
#check ExtractionSchur.rankBudgetCollisionWidth
#print axioms ExtractionSchur.rankBudgetCollisionWidth
#check ExtractionSchur.rankBudgetWidth
#print axioms ExtractionSchur.rankBudgetWidth
#check ExtractionSchur.rankBudgetPacking
#print axioms ExtractionSchur.rankBudgetPacking
#check ExtractionSchur.rankBudgetEta
#print axioms ExtractionSchur.rankBudgetEta
#check ExtractionSchur.exactRankBudgetTargets
#print axioms ExtractionSchur.exactRankBudgetTargets
#check ExtractionSchur.errorRankBudgetTargets
#print axioms ExtractionSchur.errorRankBudgetTargets
#check ExtractionSchur.exactRankBudgetMaximum
#print axioms ExtractionSchur.exactRankBudgetMaximum
#check ExtractionSchur.errorRankBudgetMaximum
#print axioms ExtractionSchur.errorRankBudgetMaximum
#check ExtractionSchur.rankBudgetLogScale
#print axioms ExtractionSchur.rankBudgetLogScale
#check ExtractionSchur.densityOrbitInput
#print axioms ExtractionSchur.densityOrbitInput
#check ExtractionSchur.orbitExactTargets
#print axioms ExtractionSchur.orbitExactTargets
#check ExtractionSchur.orbitExactMaximum
#print axioms ExtractionSchur.orbitExactMaximum
#check ExtractionSchur.flatOrbitPhysicalMinimax
#print axioms ExtractionSchur.flatOrbitPhysicalMinimax
#check ExtractionSchur.flatOrbitErrorTargets
#print axioms ExtractionSchur.flatOrbitErrorTargets
#check ExtractionSchur.flatOrbitErrorMaximum
#print axioms ExtractionSchur.flatOrbitErrorMaximum
#check ExtractionAPPT.quantumEntropy
#print axioms ExtractionAPPT.quantumEntropy
#check ExtractionAPPT.flatten
#print axioms ExtractionAPPT.flatten
#check ExtractionAPPT.apptEntropyValues
#print axioms ExtractionAPPT.apptEntropyValues
#check ExtractionAPPT.apptMinEntropy
#print axioms ExtractionAPPT.apptMinEntropy
#check ExtractionAPPT.physicalCapacity
#print axioms ExtractionAPPT.physicalCapacity
#check ExtractionAPPT.apptCapacityValues
#print axioms ExtractionAPPT.apptCapacityValues
#check ExtractionAPPT.apptMaxCapacity
#print axioms ExtractionAPPT.apptMaxCapacity
#check ExtractionAPPT.spikeState
#print axioms ExtractionAPPT.spikeState
#check ExtractionAPPT.purityCapacityBudget
#print axioms ExtractionAPPT.purityCapacityBudget
#check MinimaxProfile.KrausPPTProtocol
#print axioms MinimaxProfile.KrausPPTProtocol
#check MinimaxProfile.tensorInput
#print axioms MinimaxProfile.tensorInput
