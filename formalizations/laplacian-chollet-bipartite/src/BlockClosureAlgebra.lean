import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

namespace Chollet

/-- A universal scalar diagonal-increment inequality, needed when converting
a hereditary strong principal permanent inequality into stability under
positive diagonal updates. All hypotheses are explicit scalar inequalities;
no matrix or external permanent theorem is assumed. -/
theorem diagonal_increment_algebra
    (a h P R Q T t : ℝ)
    (ha : 0 ≤ a) (hh : 0 ≤ h) (ht : 0 ≤ t)
    (hstrong : Q ≤ a*h*P) (hminor : T ≤ h*R)
    (hpivot : a*R ≤ P) :
    Q + (2*a*t+t^2)*T ≤ h*(a+t)*(P+t*R) := by
  have h1 : 0 ≤ a*h*P-Q := sub_nonneg.mpr hstrong
  have h2 : 0 ≤ h*R-T := sub_nonneg.mpr hminor
  have h3 : 0 ≤ P-a*R := sub_nonneg.mpr hpivot
  have ident :
      h*(a+t)*(P+t*R) - (Q+(2*a*t+t^2)*T) =
      (a*h*P-Q) + t*h*(P-a*R) + (2*a*t+t^2)*(h*R-T) := by
    ring
  rw [←sub_nonneg, ident]
  positivity


/-- Exact scalar one-point-sum closure inequality. The variables are the
two block permanents P_i, their deleted-vertex permanents R_i, their
Hadamard-square permanents Q_i and T_i, the distinguished diagonals a_i
and products h_i of other diagonals. This handles all degeneracies. -/
theorem one_point_sum_algebra
    (a1 a2 h1 h2 P1 P2 R1 R2 Q1 Q2 T1 T2 : ℝ)
    (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2)
    (hh1 : 0 ≤ h1) (hh2 : 0 ≤ h2)
    (hP1 : 0 ≤ P1)
    (hR1 : 0 ≤ R1) (hR2 : 0 ≤ R2)
    (hQ2 : 0 ≤ Q2) (hT2 : 0 ≤ T2)
    (hstrong1 : Q1 ≤ a1*h1*P1)
    (hstrong2 : Q2 ≤ a2*h2*P2)
    (hminor1 : T1 ≤ h1*R1) (hminor2 : T2 ≤ h2*R2)
    (hpivot1 : a1*R1 ≤ P1) (hpivot2 : a2*R2 ≤ P2) :
    Q1*T2 + T1*Q2 + 2*a1*a2*T1*T2 ≤
      h1*h2*(a1+a2)*(P1*R2+R1*P2) := by
  have hq1 : 0 ≤ a1*h1*P1-Q1 := sub_nonneg.mpr hstrong1
  have hq2 : 0 ≤ a2*h2*P2-Q2 := sub_nonneg.mpr hstrong2
  have ht1 : 0 ≤ h1*R1-T1 := sub_nonneg.mpr hminor1
  have ht2 : 0 ≤ h2*R2-T2 := sub_nonneg.mpr hminor2
  have hp1 : 0 ≤ P1-a1*R1 := sub_nonneg.mpr hpivot1
  have hp2 : 0 ≤ P2-a2*R2 := sub_nonneg.mpr hpivot2
  have ident :
      h1*h2*(a1+a2)*(P1*R2+R1*P2) -
        (Q1*T2+T1*Q2+2*a1*a2*T1*T2) =
      h1*h2*(a2*R2*(P1-a1*R1)+a1*R1*(P2-a2*R2)) +
      (a1*h1*P1-Q1)*T2 +
      (a1*h1*P1)*(h2*R2-T2) +
      (h1*R1-T1)*Q2 +
      (h1*R1)*(a2*h2*P2-Q2) +
      2*a1*a2*((h1*R1-T1)*T2+(h1*R1)*(h2*R2-T2)) := by
    ring
  rw [←sub_nonneg, ident]
  positivity

end Chollet

#print axioms Chollet.diagonal_increment_algebra
#print axioms Chollet.one_point_sum_algebra
