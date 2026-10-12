import APPT.Quantum.Maximum
open APPT.Quantum
-- Deliberately incorrect endpoint value, paired with PositivePurity.lean.
example : targetPurity 8 = (9 : ℝ)/169 := by norm_num [targetPurity]
