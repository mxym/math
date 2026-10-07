import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-! Integer certificates used in the nineteen-edge necessary bound.
The reduction from hypergraphs to degree patterns remains a written proof.
No solver status or numerical oracle is imported. -/
namespace RyserDegreeCertificate

theorem sixteen_deficit (k : ℤ) :
    -90+18*k-3*k^2 ≤ -63 := by
  nlinarith [sq_nonneg (k-3)]

theorem seventeen_deficit (k l : ℤ) (hl : 0 ≤ l) :
    -80+24*k+11*l-(2*k+l)^2 ≤ -44 := by
  nlinarith [sq_nonneg (2*k+l-6)]

theorem eighteen_deficit (a b c d e f : ℤ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (he : 0 ≤ e) (hf : 0 ≤ f)
    (hsum : a+b+c+d+e+f = 6) :
    -10*a^2-12*a*b-6*a*c-4*a*d-2*a*e+70*a-
      3*b^2-2*b*c+38*b+20*c+15*d+5*e-135 ≤ -1 := by
  have ha6 : a ≤ 6 := by omega
  have hb6 : b ≤ 6 := by omega
  interval_cases a <;> interval_cases b <;> nlinarith

#print axioms sixteen_deficit
#print axioms seventeen_deficit
#print axioms eighteen_deficit

end RyserDegreeCertificate
