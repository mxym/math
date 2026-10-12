import EqualityCauchySaturation

namespace ComplexPencilEquality

open ComplexPencilMain
open ComplexPencilLink
open scoped ComplexConjugate

noncomputable section

private theorem conj_mul_self_eq_sq (a : ℂ) :
    (conj a)*a = ((ComplexPencilLink.sq a : ℝ) : ℂ) := by
  calc
    _ = ((Complex.normSq a : ℝ) : ℂ) :=
      (Complex.normSq_eq_conj_mul_self).symm
    _ = ((ComplexPencilLink.sq a : ℝ) : ℂ) := by
      rw [ComplexPencilFull.normSq_eq_sq]

/-- The terminal Cauchy–Schwarz comparison vector of a flat first
row and a second proportional row has conjugate entries aligned
with the original first row.  Complex phases are arbitrary. -/
theorem flat_output_phase_proportional
    (lam a0 a1 a2 z : ℂ)
    (h01 : ComplexPencilLink.sq a0 = ComplexPencilLink.sq a1)
    (h12 : ComplexPencilLink.sq a1 = ComplexPencilLink.sq a2) :
    (conj (t0 lam a1 a2 (z*a1) (z*a2)))*a1 =
      (conj (t1 lam a0 a2 (z*a0) (z*a2)))*a0 ∧
    (conj (t0 lam a1 a2 (z*a1) (z*a2)))*a2 =
      (conj (t2 lam a0 a1 (z*a0) (z*a1)))*a0 := by
  have ht0 : t0 lam a1 a2 (z*a1) (z*a2)=2*z*a1*a2 := by
    unfold t0 p0 q0 alpha beta
    ring
  have ht1 : t1 lam a0 a2 (z*a0) (z*a2)=2*z*a0*a2 := by
    unfold t1 p1 q1 alpha beta
    ring
  have ht2 : t2 lam a0 a1 (z*a0) (z*a1)=2*z*a0*a1 := by
    unfold t2 p2 q2 alpha beta
    ring
  have hc01 : (conj a0)*a0=(conj a1)*a1 := by
    rw [conj_mul_self_eq_sq, conj_mul_self_eq_sq, h01]
  have hc02 : (conj a0)*a0=(conj a2)*a2 := by
    rw [conj_mul_self_eq_sq, conj_mul_self_eq_sq, h01.trans h12]
  constructor
  · rw [ht0,ht1]
    calc
      _ = 2*(conj z)*((conj a1)*a1)*(conj a2) := by
        simp only [map_mul, map_ofNat]
        ring
      _ = 2*(conj z)*((conj a0)*a0)*(conj a2) := by rw [hc01]
      _ = _ := by
        simp only [map_mul, map_ofNat]
        ring
  · rw [ht0,ht2]
    calc
      _ = 2*(conj z)*((conj a2)*a2)*(conj a1) := by
        simp only [map_mul, map_ofNat]
        ring
      _ = 2*(conj z)*((conj a0)*a0)*(conj a1) := by rw [hc02]
      _ = _ := by
        simp only [map_mul, map_ofNat]
        ring

#print axioms ComplexPencilEquality.flat_output_phase_proportional

end
end ComplexPencilEquality
