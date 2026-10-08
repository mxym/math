import TensorNormSharp

namespace ComplexPencilDistribution

open ComplexPencilTensor

noncomputable section

/-- The three labelled one-point marginals of a law on the six
permutations of Fin 3, in the canonical even-first enumeration. -/
def margin₀ (p : Fin 6 → ℝ) (r : Fin 3) : ℝ :=
  ∑ j : Fin 6, if first j = r then p j else 0

def margin₁ (p : Fin 6 → ℝ) (r : Fin 3) : ℝ :=
  ∑ j : Fin 6, if second j = r then p j else 0

def margin₂ (p : Fin 6 → ℝ) (r : Fin 3) : ℝ :=
  ∑ j : Fin 6, if third j = r then p j else 0

def uniformMargins (p : Fin 6 → ℝ) : Prop :=
  (∀ r : Fin 3, margin₀ p r = 1 / 3) ∧
  (∀ r : Fin 3, margin₁ p r = 1 / 3) ∧
  (∀ r : Fin 3, margin₂ p r = 1 / 3)

/-- An arbitrary real signed distribution on S₃ with uniform
one-point marginals has the unique even/odd one-parameter form.
No positivity assumption is needed for this linear classification. -/
theorem uniformMargins_weight (p : Fin 6 → ℝ) (h : uniformMargins p) :
    ∃ t : ℝ, ∀ j : Fin 6, p j = weight t j := by
  rcases h with ⟨h0, h1, h2⟩
  have h00 : p 0 + p 3 = 1 / 3 := by
    simpa [margin₀, first, Fin.sum_univ_succ] using h0 0
  have h01 : p 1 + p 4 = 1 / 3 := by
    simpa [margin₀, first, Fin.sum_univ_succ] using h0 1
  have h02 : p 2 + p 5 = 1 / 3 := by
    simpa [margin₀, first, Fin.sum_univ_succ] using h0 2
  have h10 : p 2 + p 4 = 1 / 3 := by
    simpa [margin₁, second, Fin.sum_univ_succ] using h1 0
  have h11 : p 0 + p 5 = 1 / 3 := by
    simpa [margin₁, second, Fin.sum_univ_succ] using h1 1
  have h12 : p 1 + p 3 = 1 / 3 := by
    simpa [margin₁, second, Fin.sum_univ_succ] using h1 2
  have h20 : p 1 + p 5 = 1 / 3 := by
    simpa [margin₂, third, Fin.sum_univ_succ] using h2 0
  have h21 : p 2 + p 3 = 1 / 3 := by
    simpa [margin₂, third, Fin.sum_univ_succ] using h2 1
  have h22 : p 0 + p 4 = 1 / 3 := by
    simpa [margin₂, third, Fin.sum_univ_succ] using h2 2
  refine ⟨p 0 - 1 / 6, ?_⟩
  intro j
  fin_cases j <;> simp [weight] <;> linarith

/-- A nonnegative law in this family forces the sharp probability
parameter interval |t|≤1/6. -/
theorem law_parameter_bound (p : Fin 6 → ℝ)
    (hn : ∀ j, 0 ≤ p j) (h : uniformMargins p) :
    ∃ t : ℝ, |t| ≤ (1/6 : ℝ) ∧
      ∀ j, p j = weight t j := by
  obtain ⟨t, hp⟩ := uniformMargins_weight p h
  refine ⟨t, ?_, hp⟩
  have ha : 0 ≤ (1/6 : ℝ) + t := by
    simpa [hp, weight] using (hn 0)
  have hb : 0 ≤ (1/6 : ℝ) - t := by
    simpa [hp, weight] using (hn 3)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Converse: for every real t the six weights have exactly
uniform point marginals (even without positivity). -/
theorem weight_uniformMargins (t : ℝ) : uniformMargins (weight t) := by
  constructor
  · exact first_marginal_uniform t
  constructor
  · exact second_marginal_uniform t
  · exact third_marginal_uniform t

#print axioms ComplexPencilDistribution.uniformMargins_weight
#print axioms ComplexPencilDistribution.law_parameter_bound

end
end ComplexPencilDistribution
