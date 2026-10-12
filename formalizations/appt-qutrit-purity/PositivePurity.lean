import APPT.Quantum.Maximum
open APPT.Quantum
example : targetPurity 3 = (17 : ℝ)/121 := by norm_num [targetPurity]
example : targetPurity 8 = (8 : ℝ)/169 := by norm_num [targetPurity]
example : targetPurity 9 = (1 : ℝ)/24 := by norm_num [targetPurity]
#check appt_purity_maximum_formula
#print axioms appt_purity_maximum_formula
