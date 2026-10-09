import APPT.Quantum.SemanticRegression
import Verification.ReplaySupport

run_cmd APPTVerification.replayAndCorrupt [
  ``APPT.Quantum.exists_PPT_density_exceeding_target,
  ``APPT.Quantum.exists_PPT_density_not_APPT,
  ``APPT.Quantum.basisPureState_isDensity,
  ``APPT.Quantum.basisPureState_partialTranspose,
  ``APPT.Quantum.basisPureState_purity,
  ``APPT.Quantum.targetPurity_lt_one] "semantic-regression"
