import CompletionAudit
import CompletionVerification.ReplaySupport

run_cmd CompletionVerification.replayAll [
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
  ``CircuitRecursion.compressionCircuit_action,
  ``CircuitRecursion.compressionCircuit_matrix,
  ``CircuitRecursion.compressionCircuit_coherent,
  ``CircuitRecursion.compressionCircuit_purePower,
  ``CircuitRecursion.compressionCircuit_length,
  ``CircuitRecursion.compressionCircuit_polynomial_bound,
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
  ``CircuitRecursion.compressionCircuit,
  ``CircuitRecursion.bitPurePower
] "verification/completion-kernel"

run_cmd CompletionVerification.rejectCorruptTheorem ``ExtractionCP.completelyPositive_iff_choi_posSemidef "verification/completion-control-1"
run_cmd CompletionVerification.rejectCorruptTheorem ``ExtractionCP.choiKraus_complete "verification/completion-control-2"
run_cmd CompletionVerification.rejectCorruptTheorem ``ExtractionCP.abstract_ppt_iff_actual_protocol "verification/completion-control-3"
run_cmd CompletionVerification.rejectCorruptTheorem ``OperationalCompletion.reservedProtocol_guarantees "verification/completion-control-4"
run_cmd CompletionVerification.rejectCorruptTheorem ``OperationalCompletion.balanced_reserved_family_sharp "verification/completion-control-5"
run_cmd CompletionVerification.rejectCorruptTheorem ``OperationalCompletion.reserved_gaussian_limit "verification/completion-control-6"
run_cmd CompletionVerification.rejectCorruptTheorem ``OperationalCompletion.reserved_fidelity_exponent "verification/completion-control-7"
run_cmd CompletionVerification.rejectCorruptTheorem ``OperationalCompletion.reserved_reliability_limit "verification/completion-control-8"
run_cmd CompletionVerification.rejectCorruptTheorem ``OperationalCompletion.reserved_eventually_exact "verification/completion-control-9"
run_cmd CompletionVerification.rejectCorruptTheorem ``ExtractionDeviation.finite_iid_berryEsseen_sup "verification/completion-control-10"
run_cmd CompletionVerification.rejectCorruptTheorem ``ExtractionDeviation.density_information_berryEsseen "verification/completion-control-11"
run_cmd CompletionVerification.rejectCorruptTheorem ``ExtractionDeviation.informationQuantile_berryEsseen_bracket "verification/completion-control-12"
run_cmd CompletionVerification.rejectCorruptTheorem ``ExtractionDeviation.finiteCappedTarget_achievable "verification/completion-control-13"
run_cmd CompletionVerification.rejectCorruptTheorem ``ExtractionDeviation.pptFixedErrorTarget_gaussian "verification/completion-control-14"
run_cmd CompletionVerification.rejectCorruptTheorem ``ExtractionDeviation.triangular_universal_gaussian_of_variance_floor "verification/completion-control-15"
run_cmd CompletionVerification.rejectCorruptTheorem ``ExtractionSchur.flatHaarAverage_jucys_product_eigenvalue "verification/completion-control-16"
run_cmd CompletionVerification.rejectCorruptTheorem ``ExtractionSchur.flatHaarAverage_codimension_one_purity_scaled_limit "verification/completion-control-17"
run_cmd CompletionVerification.rejectCorruptTheorem ``CircuitRecursion.compressionCircuit_purePower "verification/completion-control-18"
run_cmd CompletionVerification.rejectCorruptTheorem ``CircuitRecursion.compressionCircuit_polynomial_bound "verification/completion-control-19"
