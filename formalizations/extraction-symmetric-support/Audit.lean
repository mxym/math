import SymmetricSupport
import SymmetricSupportVerification.ReplaySupport

run_cmd (SymmetricSupportVerification.replayAndCorrupt [
  ``SymmetricSupport.exact_unitPurePower_effect_mul_symmetricProjector,
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
  ``SymmetricSupport.fiberCard_pos,
  ``SymmetricSupport.average_columns,
  ``SymmetricSupport.partitionProjector_apply,
  ``SymmetricSupport.partitionProjector_idempotent,
  ``SymmetricSupport.partitionProjector_hermitian,
  ``SymmetricSupport.partitionProjector_rank,
  ``SymmetricSupport.partitionProjector_mulVec_constant,
  ``SymmetricSupport.occupation_surjective,
  ``SymmetricSupport.purePower_equal_occupation,
  ``SymmetricSupport.symmetricProjector_hermitian,
  ``SymmetricSupport.symmetricProjector_idempotent,
  ``SymmetricSupport.symmetricProjector_fixes_purePower,
  ``SymmetricSupport.symmetricProjector_rank_choose,
  ``SymmetricSupport.symmetricProjector_rank_choose_complement,
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

run_cmd SymmetricSupportVerification.rejectCorruptTheorem ``SymmetricSupport.symmetricProjector_rank_choose_complement "verification/symmetric-control-1"

run_cmd SymmetricSupportVerification.rejectCorruptTheorem ``SymmetricSupport.symmetricProjector_range_eq_unitPurePower_span "verification/symmetric-control-2"

run_cmd SymmetricSupportVerification.rejectCorruptTheorem ``SymmetricSupport.symmetricState_purity "verification/symmetric-control-3"

run_cmd SymmetricSupportVerification.rejectCorruptTheorem ``SymmetricSupport.purePowerDensity_supported "verification/symmetric-control-4"

run_cmd SymmetricSupportVerification.rejectCorruptTheorem ``SymmetricSupport.monomialCoordinates_span_top "verification/symmetric-control-5"
