import APPT.Quantum.Maximum
import APPT.SparsePolynomial

namespace APPTVerification
open APPT.Quantum

-- These controls cover both endpoints of the finite branch and the first
-- large dimension. They are not substitutes for the universally quantified root.
example : targetPurity 3 = (17 : ℝ)/121 := by norm_num [targetPurity]
example : targetPurity 8 = (8 : ℝ)/169 := by norm_num [targetPurity]
example : targetPurity 9 = (1 : ℝ)/24 := by norm_num [targetPurity]

example : IsGreatest (attainablePurities 3) ((17 : ℝ)/121) := by
  convert targetPurity_isGreatest 3 (by norm_num) using 1 <;> norm_num [targetPurity]

example : IsGreatest (attainablePurities 8) ((8 : ℝ)/169) := by
  convert targetPurity_isGreatest 8 (by norm_num) using 1 <;> norm_num [targetPurity]

example : IsGreatest (attainablePurities 9) ((1 : ℝ)/24) := by
  convert targetPurity_isGreatest 9 (by norm_num) using 1 <;> norm_num [targetPurity]

example : APPT.SparsePolynomial.trim
    (APPT.SparsePolynomial.mul [([0],1),([1],1)]
      (APPT.SparsePolynomial.mul [([0],1),([1],1)] [([0],1),([1],1)])) =
    [([0,0,0],1),([0,0,1],3),([0,1,1],3),([1,1,1],1)] :=
  APPT.SparsePolynomial.cubic_control

end APPTVerification
