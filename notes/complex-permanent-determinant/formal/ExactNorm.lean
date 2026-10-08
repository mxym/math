import Witnesses

namespace ComplexPencilFull
open ComplexPencilMain
open ComplexPencilLink

noncomputable section

def universalSquaredBound (lam : ℂ) (B : ℝ) : Prop :=
   ∀ a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℂ,
     ComplexPencilLink.sq (permanent3 a0 a1 a2 b0 b1 b2 c0 c1 c2+
          lam*determinant3 a0 a1 a2 b0 b1 b2 c0 c1 c2) ≤
      B*rowSq a0 a1 a2*rowSq b0 b1 b2*rowSq c0 c1 c2

theorem universalSquaredBound_of_ge
    (lam : ℂ) (B : ℝ) (h : normBoundSq lam ≤ B) :
    universalSquaredBound lam B := by
  intro a0 a1 a2 b0 b1 b2 c0 c1 c2
  have ha : 0 ≤ rowSq a0 a1 a2 := by
    unfold rowSq
    have hx := sq_nonneg a0
    have hy := sq_nonneg a1
    have hz := sq_nonneg a2
    linarith
  have hb : 0 ≤ rowSq b0 b1 b2 := by
    unfold rowSq
    have hx := sq_nonneg b0
    have hy := sq_nonneg b1
    have hz := sq_nonneg b2
    linarith
  have hc : 0 ≤ rowSq c0 c1 c2 := by
    unfold rowSq
    have hx := sq_nonneg c0
    have hy := sq_nonneg c1
    have hz := sq_nonneg c2
    linarith
  have hn := exact_norm_upper lam a0 a1 a2 b0 b1 b2 c0 c1 c2
  calc
    _ ≤ normBoundSq lam *
          (rowSq a0 a1 a2*rowSq b0 b1 b2*rowSq c0 c1 c2) := by
           simpa only [mul_assoc] using hn
    _ ≤ B*(rowSq a0 a1 a2*rowSq b0 b1 b2*rowSq c0 c1 c2) := by
         exact mul_le_mul_of_nonneg_right h
           (mul_nonneg (mul_nonneg ha hb) hc)
    _ = _ := by ring

theorem universalSquaredBound_le (lam : ℂ) (B : ℝ)
    (h : universalSquaredBound lam B) : normBoundSq lam ≤ B := by
  have hon := h 1 1 1 1 1 1 1 1 1
  have hbase : (4/3:ℝ) ≤ B := by
    norm_num [permanent3,determinant3,rowSq,ComplexPencilLink.sq] at hon
    nlinarith
  have heven := h 1 0 0 0 1 0 0 0 1
  have hodd := h 1 0 0 0 0 1 0 1 0
  have hp : 1+qval lam+2*lam.re ≤ B := by
    have ht : ComplexPencilLink.sq (1+lam) ≤ B := by
      simpa [permanent3,determinant3,rowSq,ComplexPencilLink.sq] using heven
    change ComplexPencilLink.sq (beta lam) ≤ B at ht
    rw [sq_beta] at ht
    exact ht
  have hm : 1+qval lam-2*lam.re ≤ B := by
    have ht : ComplexPencilLink.sq (1-lam) ≤ B := by
      simpa [permanent3,determinant3,rowSq,ComplexPencilLink.sq,
        sub_eq_add_neg] using hodd
    change ComplexPencilLink.sq (alpha lam) ≤ B at ht
    rw [sq_alpha] at ht
    exact ht
  have hfminus : qval lam+1/3-(2*rt3/3)*lam.im ≤ B := by
    have ht := h 1 1 1 1 omega omegaBar 1 omegaBar omega
    have ⟨ha,hb,hc⟩ := witness_rows
    rw [fourier_minus_exact,ha,hb,hc] at ht
    nlinarith
  have hfplus : qval lam+1/3+(2*rt3/3)*lam.im ≤ B := by
    have ht := h 1 1 1 1 omegaBar omega 1 omega omegaBar
    have ⟨ha,hb,hc⟩ := witness_rows
    rw [fourier_plus_exact,ha,hc,hb] at ht
    nlinarith
  unfold normBoundSq
  exact max_le hbase (max_le hp (max_le hm (max_le hfplus hfminus)))

/-- Complete Theorem 1B: every complex pencil coefficient and its
    exact sharp squared Euclidean 3-row norm, including outside
    the coefficient lens. -/
theorem sharp_full_pencil_norm_iff (lam : ℂ) (B : ℝ) :
    universalSquaredBound lam B ↔ normBoundSq lam ≤ B := by
  constructor
  · exact universalSquaredBound_le lam B
  · exact universalSquaredBound_of_ge lam B

#print axioms ComplexPencilFull.sharp_full_pencil_norm_iff

end
end ComplexPencilFull
