import PermutationMarginalsIndependent
import RealLawNorm
import AbsolutePencil

namespace ComplexPencilProbability
open ComplexPencilTensor
open ComplexPencilReal
open ComplexPencilFull
open ComplexPencilAbsolute
noncomputable section

def tvThreshold : ℝ := detWeight / 2

theorem law_contractive_iff_tv (t : ℝ) :
    LawBound t 1 ↔ 3 * |t| ≤ tvThreshold := by
  rw [law_bound_exact]
  have hρ := rho_sq
  have hρpos := rho_pos
  have ht : 0 ≤ |t| := abs_nonneg t
  have hfun : |6*t| = 6*|t| := by
    rw [abs_mul]
    norm_num
  unfold tvThreshold
  constructor
  · intro hh
    have hco : (3/4:ℝ)*(1+|6*t|)^2 ≤ 1 :=
      (le_max_right _ _).trans hh
    rw [hfun] at hco
    have hs : (1+6*|t|)^2 ≤ rho^2 := by nlinarith [hρ]
    have hnon : 0 ≤ 1+6*|t| := by positivity
    have hx : 1+6*|t| ≤ rho := by nlinarith
    unfold detWeight
    linarith
  · intro hh
    unfold detWeight at hh
    have hx : 1+6*|t| ≤ rho := by linarith
    have hnon : 0 ≤ 1+6*|t| := by positivity
    have hsq : (1+6*|t|)^2 ≤ rho^2 := by
      nlinarith [mul_nonneg
        (sub_nonneg.mpr hx)
        (add_nonneg (le_of_lt hρpos) hnon)]
    have hco : (3/4:ℝ)*(1+|6*t|)^2 ≤ 1 := by
      rw [hfun]
      nlinarith [hρ]
    exact max_le (le_refl _) hco

/-- The sharp TV threshold for a uniform-marginal S₃ law,
    phrased through its unique parity parameter. -/
theorem sharp_tv_parameter_iff (t : ℝ) :
    LawBound t 1 ↔
      parityTV (weight t) ≤ tvThreshold := by
  rw [law_contractive_iff_tv, parityTV_weight]

/-- Any probability law on S₃ with uniform one-point marginals
    has a unique parity parameter and its TV is exactly 3|t|.
    The law is L²-contractive if and only if the TV threshold holds. -/
theorem uniform_probability_law_classified
    (p : Fin 6 → ℝ)
    (hm : uniformMarginals p)
    (hp : ∀ j, 0 ≤ p j) :
    ∃! t : ℝ,
      p = weight t ∧ |t| ≤ (1/6 : ℝ) ∧
        parityTV p = 3 * |t| ∧
        (LawBound t 1 ↔ parityTV p ≤ tvThreshold) := by
  obtain ⟨t, rfl⟩ := (uniformMarginals_iff_parity p).mp hm
  have ht := (nonneg_weight_iff t).mp hp
  refine ⟨t, ⟨rfl, ht, parityTV_weight t, ?_⟩, ?_⟩
  · exact sharp_tv_parameter_iff t
  · intro s hs
    exact (parity_parameter_unique t s hs.1).symm

#print axioms ComplexPencilProbability.uniform_probability_law_classified

end
end ComplexPencilProbability
