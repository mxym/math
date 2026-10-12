import TensorSemantics

namespace ComplexPencilProbability
open ComplexPencilTensor

noncomputable section

def firstMarginal (p : Fin 6 → ℝ) (r : Fin 3) : ℝ :=
  ∑ j : Fin 6, if first j = r then p j else 0

def secondMarginal (p : Fin 6 → ℝ) (r : Fin 3) : ℝ :=
  ∑ j : Fin 6, if second j = r then p j else 0

def thirdMarginal (p : Fin 6 → ℝ) (r : Fin 3) : ℝ :=
  ∑ j : Fin 6, if third j = r then p j else 0

def uniformMarginals (p : Fin 6 → ℝ) : Prop :=
  (∀ r, firstMarginal p r = 1/3) ∧
  (∀ r, secondMarginal p r = 1/3) ∧
  (∀ r, thirdMarginal p r = 1/3)

theorem uniformMarginals_of_weight (t : ℝ) :
    uniformMarginals (weight t) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r
    exact first_marginal_uniform t r
  · intro r
    exact second_marginal_uniform t r
  · intro r
    exact third_marginal_uniform t r

/-- Every real six-outcome signed distribution with uniform
    coordinate marginals has even/odd parity weights determined
    by one real parameter; no positivity or total-mass
    assumptions are needed for this exact affine assertion. -/
theorem uniformMarginals_iff_parity (p : Fin 6 → ℝ) :
    uniformMarginals p ↔ ∃ t : ℝ, p = weight t := by
  constructor
  · rintro ⟨hfirst,hsecond,hthird⟩
    have h03 : p 0 + p 3 = (1/3:ℝ) := by
      have h := hfirst 0
      simp [firstMarginal, first, Fin.sum_univ_succ] at h
      linarith
    have h14 : p 1 + p 4 = (1/3:ℝ) := by
      have h := hfirst 1
      simp [firstMarginal, first, Fin.sum_univ_succ] at h
      linarith
    have h25 : p 2 + p 5 = (1/3:ℝ) := by
      have h := hfirst 2
      simp [firstMarginal, first, Fin.sum_univ_succ] at h
      linarith
    have h13 : p 1 + p 3 = (1/3:ℝ) := by
      have h := hsecond 2
      simp [secondMarginal, second, Fin.sum_univ_succ] at h
      linarith
    have h23 : p 2 + p 3 = (1/3:ℝ) := by
      have h := hthird 1
      simp [thirdMarginal, third, Fin.sum_univ_succ] at h
      linarith
    refine ⟨p 0 - 1/6, ?_⟩
    funext j
    fin_cases j <;> simp [weight] <;>
      linarith [h03,h14,h25,h13,h23]
  · rintro ⟨t, rfl⟩
    exact uniformMarginals_of_weight t

theorem parity_parameter_unique (s t : ℝ)
    (heq : weight s = weight t) : s = t := by
  have h := congrFun heq 0
  change (1/6:ℝ)+s = (1/6:ℝ)+t at h
  linarith

theorem parity_total_mass (t : ℝ) :
    (∑ j : Fin 6, weight t j) = 1 :=
  weight_total_one t

def parityTV (p : Fin 6 → ℝ) : ℝ :=
  (∑ j : Fin 6, |p j - 1/6|)/2

theorem parityTV_weight (t : ℝ) :
    parityTV (weight t) = 3 * |t| := by
  simp [parityTV,weight,Fin.sum_univ_succ,
    abs_neg, abs_mul]
  ring

theorem nonneg_weight_iff (t : ℝ) :
    (∀ j : Fin 6, 0 ≤ weight t j) ↔ |t| ≤ (1/6:ℝ) := by
  constructor
  · intro h
    have hp := h 0
    have hm := h 3
    simp [weight] at hp hm
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  · intro ht j
    exact weight_nonneg t ht j

#print axioms ComplexPencilProbability.uniformMarginals_iff_parity
#print axioms ComplexPencilProbability.parityTV_weight

end
end ComplexPencilProbability
