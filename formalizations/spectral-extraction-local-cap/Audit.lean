import ExtractionLocalCap
import LocalCapVerification.ReplaySupport

run_cmd (LocalCapVerification.replayAndCorrupt [
  ``ExtractionLocalCap.kraus_target_overlap_full_envelope,
  ``ExtractionLocalCap.kraus_target_overlap_unitary_local_cap,
  ``ExtractionLocalCap.local_order_cap,
  ``ExtractionLocalCap.pure_partialTranspose_pairing_le,
  ``ExtractionLocalCap.rainsEffect_local_order_cap,
  ``ExtractionLocalCap.rainsEffect_density_overlap_le,
  ``ExtractionLocalCap.kraus_target_overlap_local_cap,
  ``ExtractionLocalCap.compression_order_interval,
  ``ExtractionLocalCap.order_interval_diagonal,
  ``ExtractionLocalCap.trace_signed_congruence_le,
  ``ExtractionLocalCap.schmidtSigned_absolute_mass
] "verification/local-cap-kernel")

run_cmd LocalCapVerification.rejectCorruptTheorem ``ExtractionLocalCap.kraus_target_overlap_unitary_local_cap "verification/local-cap-control-1"
run_cmd LocalCapVerification.rejectCorruptTheorem ``ExtractionLocalCap.local_order_cap "verification/local-cap-control-2"
run_cmd LocalCapVerification.rejectCorruptTheorem ``ExtractionLocalCap.pure_partialTranspose_pairing_le "verification/local-cap-control-3"
run_cmd LocalCapVerification.rejectCorruptTheorem ``ExtractionLocalCap.schmidtSigned_absolute_mass "verification/local-cap-control-4"
run_cmd LocalCapVerification.rejectCorruptTheorem ``ExtractionLocalCap.compression_order_interval "verification/local-cap-control-5"
