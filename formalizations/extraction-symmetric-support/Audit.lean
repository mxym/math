import SymmetricSupport
import SymmetricSupportVerification.ReplaySupport

run_cmd (SymmetricSupportVerification.replayAndCorrupt [
  ``SymmetricSupport.pure_guarantee_le_symmetricState,
  ``SymmetricSupport.partitionProjector_trace,
  ``SymmetricSupport.symmetricProjector_trace,
  ``SymmetricSupport.symmetricProjector_posSemidef,
  ``SymmetricSupport.symmetricState_posSemidef,
  ``SymmetricSupport.occupation_card_pos,
  ``SymmetricSupport.symmetricState_trace,
  ``SymmetricSupport.symmetricState_purity,
  ``SymmetricSupport.purePowerDensity_posSemidef,
  ``SymmetricSupport.purePowerDensity_trace,
  ``SymmetricSupport.purePowerDensity_trace_one,
  ``SymmetricSupport.purePowerDensity_supported,
  ``SymmetricSupport.unit_effect_fixes_purePower,
  ``SymmetricSupport.exact_unitPurePower_effect_mul_symmetricProjector,
  ``SymmetricSupport.integral_exponential_moment,
  ``SymmetricSupport.integrable_exponential_moment,
  ``SymmetricSupport.integral_product_exponential_moment,
  ``SymmetricSupport.occupationExponent_sum,
  ``SymmetricSupport.product_X_occupation,
  ``SymmetricSupport.fiberCard_occupation_eq_multinomial,
  ``SymmetricSupport.fiberCard_mul_occupation_factorials,
  ``SymmetricSupport.fiberCard_pos,
  ``SymmetricSupport.average_columns,
  ``SymmetricSupport.partitionProjector_apply,
  ``SymmetricSupport.partitionProjector_idempotent,
  ``SymmetricSupport.partitionProjector_hermitian,
  ``SymmetricSupport.partitionProjector_rank,
  ``SymmetricSupport.partitionProjector_mulVec_constant,
  ``SymmetricSupport.occupationExponent_le,
  ``SymmetricSupport.occupation_amplitude_eq_product,
  ``SymmetricSupport.purePower_eq_product_occupation,
  ``SymmetricSupport.phase_multi_correlation,
  ``SymmetricSupport.phaseRadialAverage_apply,
  ``SymmetricSupport.radialMeasure_ae_positive,
  ``SymmetricSupport.radialMoment_integrable,
  ``SymmetricSupport.radialMoment_integral,
  ``SymmetricSupport.phaseRadialAverage_weighted_ae,
  ``SymmetricSupport.phaseRadialAverage_weighted_integrable,
  ``SymmetricSupport.phaseRadialAverage_weighted_integral,
  ``SymmetricSupport.occupation_surjective,
  ``SymmetricSupport.purePower_equal_occupation,
  ``SymmetricSupport.symmetricProjector_hermitian,
  ``SymmetricSupport.symmetricProjector_idempotent,
  ``SymmetricSupport.symmetricProjector_fixes_purePower,
  ``SymmetricSupport.symmetricProjector_rank_choose,
  ``SymmetricSupport.symmetricProjector_rank_choose_complement,
  ``SymmetricSupport.phaseRoot_primitive,
  ``SymmetricSupport.sum_root_powers_zero,
  ``SymmetricSupport.phase_correlation,
  ``SymmetricSupport.phase_correlation_star,
  ``SymmetricSupport.ofReal_mul_re,
  ``SymmetricSupport.exists_unitVector_multiple_of_pos,
  ``SymmetricSupport.purePowerDensity_smul,
  ``SymmetricSupport.pure_guarantee_homogeneous,
  ``SymmetricSupport.phaseRadialAverage_eq_real_average,
  ``SymmetricSupport.phaseRadialAverage_guarantee,
  ``SymmetricSupport.weighted_trace_expansion,
  ``SymmetricSupport.weighted_trace_integrable,
  ``SymmetricSupport.weighted_trace_integral,
  ``SymmetricSupport.weighted_real_trace_integrable,
  ``SymmetricSupport.weighted_real_trace_integral,
  ``SymmetricSupport.occupationExponent_injective,
  ``SymmetricSupport.eval_monomial_multiset,
  ``SymmetricSupport.monomialCoordinates_span_top,
  ``SymmetricSupport.purePower_occupationCoordinates,
  ``SymmetricSupport.occupationColumns_mem_purePower_span,
  ``SymmetricSupport.symmetricProjector_range_eq_purePower_span,
  ``SymmetricSupport.purePower_smul,
  ``SymmetricSupport.purePower_zero,
  ``SymmetricSupport.exists_unitVector_multiple,
  ``SymmetricSupport.purePower_mem_unitPurePower_span,
  ``SymmetricSupport.symmetricProjector_range_eq_unitPurePower_span,
  ``SymmetricSupport.unitVector_trace,
  ``SymmetricSupport.fixes_unitPurePower_mul_symmetricProjector
] "verification/symmetric-kernel")

run_cmd SymmetricSupportVerification.rejectCorruptTheorem ``SymmetricSupport.exact_unitPurePower_effect_mul_symmetricProjector "verification/symmetric-control-1"

run_cmd SymmetricSupportVerification.rejectCorruptTheorem ``SymmetricSupport.phaseRadialAverage_weighted_integral "verification/symmetric-control-2"

run_cmd SymmetricSupportVerification.rejectCorruptTheorem ``SymmetricSupport.phaseRadialAverage_apply "verification/symmetric-control-3"

run_cmd SymmetricSupportVerification.rejectCorruptTheorem ``SymmetricSupport.fiberCard_mul_occupation_factorials "verification/symmetric-control-4"

run_cmd SymmetricSupportVerification.rejectCorruptTheorem ``SymmetricSupport.integral_product_exponential_moment "verification/symmetric-control-5"

run_cmd SymmetricSupportVerification.rejectCorruptTheorem ``SymmetricSupport.symmetricProjector_rank_choose_complement "verification/symmetric-control-6"

run_cmd SymmetricSupportVerification.rejectCorruptTheorem ``SymmetricSupport.symmetricProjector_range_eq_unitPurePower_span "verification/symmetric-control-7"

run_cmd SymmetricSupportVerification.rejectCorruptTheorem ``SymmetricSupport.symmetricState_purity "verification/symmetric-control-8"

run_cmd SymmetricSupportVerification.rejectCorruptTheorem ``SymmetricSupport.purePowerDensity_supported "verification/symmetric-control-9"

run_cmd SymmetricSupportVerification.rejectCorruptTheorem ``SymmetricSupport.monomialCoordinates_span_top "verification/symmetric-control-10"
