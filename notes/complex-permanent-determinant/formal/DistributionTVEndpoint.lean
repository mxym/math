import PermutationMoment

namespace ComplexPencilDistribution

open ComplexPencilTensor
open ComplexPencilReal

noncomputable section

/-- Full sharp complex 3-row permutation inequality, for an arbitrary
nonnegative law on S₃ with uniform one-point marginals: the threshold
is stated directly in terms of its original six probabilities. -/
theorem uniformMargins_exact_TV_endpoint (p : Fin 6 → ℝ)
    (hn : ∀ j, 0 ≤ p j) (hu : uniformMargins p) :
    expectationBound p ↔
      totalVariation p ≤ ComplexPencilAbsolute.detWeight / 2 := by
  obtain ⟨t, ht, hp⟩ := law_parameter_bound p hn hu
  have hpeq : p = weight t := funext hp
  rw [hpeq, expectationBound_weight_iff,
      law_bound_one_iff_tv, variation_weight]

/-- All three margins determine a unique parity parameter. -/
theorem parity_bias_unique (t u : ℝ)
    (h : ∀ j : Fin 6, weight t j = weight u j) : t = u := by
  have h0 := h 0
  simp [weight] at h0
  linarith

theorem uniformMarginals_unique_t (p : Fin 6 → ℝ)
    (hu : uniformMargins p) :
    ∃! t : ℝ, ∀ j : Fin 6, p j = weight t j := by
  obtain ⟨t, ht⟩ := uniformMargins_weight p hu
  refine ⟨t, ht, ?_⟩
  intro u hu'
  exact (parity_bias_unique t u (fun j => (ht j).symm.trans (hu' j))).symm

#print axioms ComplexPencilDistribution.uniformMargins_exact_TV_endpoint
#print axioms ComplexPencilDistribution.uniformMarginals_unique_t

end
end ComplexPencilDistribution
