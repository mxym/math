import NormCanonical

namespace ComplexPencilReal
open ComplexPencilFull
open ComplexPencilMain
open ComplexPencilLink

noncomputable section

theorem qval_real (t : ℝ) : qval (t : ℂ) = t^2 := by
  change (ComplexPencilLink.sq (t : ℂ)) = t^2
  simp [ComplexPencilLink.sq, Complex.ofReal_re,
    Complex.ofReal_im, pow_two]

theorem normBoundSq_real (t : ℝ) :
    normBoundSq (t : ℂ) = max (4/3:ℝ) ((1+|t|)^2) := by
  let B : ℝ := max (4/3:ℝ) ((1+|t|)^2)
  have hB : (4/3:ℝ)≤B := by dsimp [B]; exact le_max_left _ _
  have hh : (1+|t|)^2≤B := by dsimp [B]; exact le_max_right _ _
  have hpos : 0≤|t| := abs_nonneg _
  have habs := le_abs_self t
  have habsneg := neg_le_abs t
  have hsq : 0≤t^2 := sq_nonneg t
  have ha : 1+t^2+2*t≤B := by nlinarith [sq_abs t]
  have hb : 1+t^2-2*t≤B := by nlinarith [sq_abs t]
  have hc : t^2+1/3≤B := by nlinarith [sq_abs t]
  have hcurve : normBoundSq (t:ℂ)≤B := by
    unfold normBoundSq
    rw [qval_real]
    simp only [Complex.ofReal_re,Complex.ofReal_im,
       mul_zero,add_zero,sub_zero]
    exact max_le hB (max_le ha (max_le hb (max_le hc hc)))
  have hbound : B≤normBoundSq (t:ℂ) := by
    dsimp [B]
    apply max_le
    · exact bound_base _
    · rcases le_total 0 t with ht | ht
      · rw [abs_of_nonneg ht]
        have hh := bound_plus (t:ℂ)
        rw [qval_real] at hh
        simp only [Complex.ofReal_re] at hh
        nlinarith
      · rw [abs_of_nonpos ht]
        have hh := bound_minus (t:ℂ)
        rw [qval_real] at hh
        simp only [Complex.ofReal_re] at hh
        nlinarith
  exact le_antisymm hcurve hbound

#print axioms ComplexPencilReal.normBoundSq_real
end
end ComplexPencilReal
