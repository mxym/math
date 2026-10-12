import UniformMarginals
import AbsolutePencil

namespace ComplexPencilDistribution
open ComplexPencilTensor
open ComplexPencilReal
open ComplexPencilFull

noncomputable section

/-- Total variation distance from the uniform measure on the six
permutations; weights need only sum to one. -/
def totalVariation (p : Fin 6 → ℝ) : ℝ :=
  (∑ j : Fin 6, |p j - (1/6 : ℝ)|) / 2

theorem variation_weight (t : ℝ) :
    totalVariation (weight t) = 3 * |t| := by
  unfold totalVariation
  simp [weight, Fin.sum_univ_succ, abs_neg]
  ring

/-- Optimal three-row norm in the centred regime is one exactly
up to the largest total-variation coefficient. -/
theorem law_bound_one_iff (t : ℝ) :
    LawBound t 1 ↔ 6 * |t| ≤ ComplexPencilAbsolute.detWeight := by
  rw [law_bound_exact]
  have hr : (0:ℝ) < ComplexPencilFull.rho :=
     ComplexPencilFull.rho_pos
  have hrr : ComplexPencilFull.rho ^ 2 = (4/3:ℝ) :=
     ComplexPencilFull.rho_sq
  have habs : |6*t| = 6*|t| := by
    simp [abs_mul]
  unfold ComplexPencilAbsolute.detWeight
  constructor
  · intro h
    have hsq : (3/4:ℝ) * (1+|6*t|)^2 ≤ 1 :=
      le_trans (le_max_right _ _) h
    rw [habs] at hsq
    have hp : 0 ≤ 1+6*|t| := by positivity
    have hp2 : (1+6*|t|)^2 ≤ ComplexPencilFull.rho^2 := by
      nlinarith
    nlinarith
  · intro h
    apply max_le
    · norm_num
    · rw [habs]
      have hx : 0 ≤ 1+6*|t| := by positivity
      have hxx : 1+6*|t| ≤ ComplexPencilFull.rho := by linarith
      nlinarith [sq_nonneg (ComplexPencilFull.rho-(1+6*|t|))]

theorem law_bound_one_iff_tv (t : ℝ) :
    LawBound t 1 ↔
      3*|t| ≤ ComplexPencilAbsolute.detWeight/2 := by
  rw [law_bound_one_iff]
  constructor <;> intro h <;> linarith

/-- The probability classification and TV formula, without assuming
the law is encoded a priori by its even/odd parity bias. -/
theorem marginal_classification_tv (p : Fin 6 → ℝ)
    (h0 : ∀ j, 0 ≤ p j) (hu : uniformMargins p) :
    ∃ t : ℝ, |t| ≤ (1/6 : ℝ) ∧
      (∀ j, p j = weight t j) ∧
      totalVariation p = 3*|t| := by
  obtain ⟨t, ht, hp⟩ := law_parameter_bound p h0 hu
  refine ⟨t, ht, hp, ?_⟩
  have eq : p = weight t := funext hp
  rw [eq, variation_weight]

#print axioms ComplexPencilDistribution.marginal_classification_tv
#print axioms ComplexPencilDistribution.law_bound_one_iff_tv

end
end ComplexPencilDistribution
