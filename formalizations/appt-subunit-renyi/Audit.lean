import APPTSubunit
import Verification.ReplaySupport

run_cmd (APPTVerification.replayAndCorrupt [
  ``APPTSubunit.halfEntropyHead_le_two,
  ``APPTSubunit.halfEntropyHead_endpoint,
  ``APPTSubunit.sorted_halfEntropyHead_from_budget,
  ``APPTSubunit.density_appt_halfEntropyHead_at_pivot,
  ``APPTSubunit.density_appt_paper_halfEntropyHead,
  ``APPTSubunit.half_polynomial_box_0,
  ``APPTSubunit.half_polynomial_box_1,
  ``APPTSubunit.half_polynomial_box_2,
  ``APPTSubunit.half_polynomial_box_3,
  ``APPTSubunit.half_polynomial_box_4,
  ``APPTSubunit.half_polynomial_box_5,
  ``APPTSubunit.half_polynomial_box_6,
  ``APPTSubunit.halfHeadPolynomial_nonneg,
  ``APPTSubunit.halfEntropyGap_lower,
  ``APPTSubunit.halfEntropyGap_nonneg,
  ``APPTSubunit.half_head_rational_comparison,
  ``APPTSubunit.half_head_scalar_comparison,
  ``APPTSubunit.half_kernel_negative_bounded,
  ``APPTSubunit.negative_even_support_card,
  ``APPTSubunit.negative_even_physical_control,
  ``APPTSubunit.naiveNegative_density,
  ``APPTSubunit.naiveNegative_not_appt,
  ``APPTSubunit.pure_negative_witness,
  ``APPTSubunit.negativeSpike_hermitian,
  ``APPTSubunit.negativeSpike_quadratic,
  ``APPTSubunit.negativeSpike_partialTranspose_posSemidef,
  ``APPTSubunit.negativeSpike_absolutelyPPT,
  ``APPTSubunit.negative_joint_coordinate,
  ``APPTSubunit.negative_joint_background,
  ``APPTSubunit.negative_joint_signed,
  ``APPTSubunit.negativeStateBase_eq,
  ``APPTSubunit.negativeStateBase_trace,
  ``APPTSubunit.negativeTrace_pos,
  ``APPTSubunit.negativeSpikeSize_nonneg,
  ``APPTSubunit.negativeState_density,
  ``APPTSubunit.negativeState_appt,
  ``APPTSubunit.negativeStateBase_square,
  ``APPTSubunit.negativeState_purity,
  ``APPTSubunit.exists_negative_rank_state
  ] "subunit-kernel")

run_cmd APPTVerification.rejectCorruptTheorem ``APPTSubunit.density_appt_paper_halfEntropyHead "subunit-control-density_appt_paper_halfEntropyHead"

run_cmd APPTVerification.rejectCorruptTheorem ``APPTSubunit.negativeSpike_absolutelyPPT "subunit-control-negativeSpike_absolutelyPPT"

run_cmd APPTVerification.rejectCorruptTheorem ``APPTSubunit.exists_negative_rank_state "subunit-control-exists_negative_rank_state"

run_cmd APPTVerification.rejectCorruptTheorem ``APPTSubunit.halfHeadPolynomial_nonneg "subunit-control-halfHeadPolynomial_nonneg"

run_cmd APPTVerification.rejectCorruptTheorem ``APPTSubunit.naiveNegative_not_appt "subunit-control-naiveNegative_not_appt"
