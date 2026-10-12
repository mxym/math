import APPT.Quantum.Maximum
import Verification.ReplaySupport

-- The full positive maximum proof is independently replayed first by
-- CheckpointReplay.lean in reproduce.py. This paired negative control keeps
-- exactly the same theorem name, type and universe parameters and replaces
-- only its proof. It uses the changed declaration's exact dependency closure.
run_cmd do
  APPTVerification.rejectCorruptTheorem ``APPT.Quantum.appt_purity_maximum_formula "completion-replayed"
