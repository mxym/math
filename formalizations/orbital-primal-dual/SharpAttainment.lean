import CentralReduction

open scoped BigOperators

namespace OrbitalMarginals

noncomputable section

variable {I J : Type*} [Fintype I] [Nonempty I]

theorem optimal_pair_tv_one (A : J → I → ℝ) (i : I) (p q : I → ℝ)
    (hp : Probability p) (hq : Probability q) (hm : Match A p q)
    (hpos : 0 < p i - q i) (hb : PairBound A i (p i - q i)) :
    TV (fun g => p g - q g) = 1 := by
  have hs := (signedBound_iff_pairBound A i (p i - q i) hpos.le).mpr hb
  have hh := hs _ (kernel_of_match A p q hp hq hm)
  rw [abs_of_pos hpos] at hh
  have hu := tv_probability_difference_le_one p q hp hq
  apply le_antisymm hu
  nlinarith

theorem probability_parts_disjoint_of_tv_one (p q : I → ℝ)
    (hp : Probability p) (hq : Probability q)
    (htv : TV (fun g => p g - q g) = 1) : ∀ g, p g = 0 ∨ q g = 0 := by
  let f : I → ℝ := fun g => p g + q g - |p g - q g|
  have hf : ∀ g, 0 ≤ f g := by
    intro g
    dsimp [f]
    have hh := abs_sub (p g) (q g)
    rw [abs_of_nonneg (hp.1 g), abs_of_nonneg (hq.1 g)] at hh
    linarith
  have hsum : ∑ g, f g = 0 := by
    have habs : ∑ g, |p g - q g| = 2 := by dsimp [TV] at htv; linarith
    simp only [f, Finset.sum_sub_distrib, Finset.sum_add_distrib, hp.2, hq.2, habs]
    norm_num
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg fun g _ => hf g).mp hsum
  intro g
  have hz := hzero g (Finset.mem_univ g)
  dsimp [f] at hz
  by_cases h : q g ≤ p g
  · right
    rw [abs_of_nonneg (sub_nonneg.mpr h)] at hz
    linarith
  · left
    rw [abs_of_neg (sub_neg.mpr (lt_of_not_ge h))] at hz
    linarith

theorem probability_perturbation_smaller (v : I → ℝ) (ε δ : ℝ)
    (hδ : 0 ≤ δ) (hle : δ ≤ ε)
    (hp : Probability (fun g => uniform g + ε * v g))
    (hv : ∑ g, v g = 0) : Probability (fun g => uniform g + δ * v g) := by
  constructor
  · intro g
    by_cases h : 0 ≤ v g
    · exact add_nonneg (uniform_pos g).le (mul_nonneg hδ h)
    · have hh := mul_le_mul_of_nonpos_right hle (le_of_not_ge h)
      linarith [hp.1 g]
  · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hv, mul_zero, add_zero]
    exact uniform_probability.2

theorem perturbation_match (A : J → I → ℝ) (v : I → ℝ)
    (hv : Kernel A v) (δ : ℝ) :
    Match A (fun g => uniform g + δ * v g) uniform := by
  intro j
  simp only [mul_add, mul_left_comm (A j _) δ, Finset.sum_add_distrib,
    ← Finset.mul_sum, hv.2 j, mul_zero, add_zero]

theorem positive_optimum_attained_locally (A : J → I → ℝ) (i : I)
    (p q : I → ℝ) (hp : Probability p) (hq : Probability q) (hm : Match A p q)
    (hpos : 0 < p i - q i) (hb : PairBound A i (p i - q i)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 ≤ δ → δ ≤ ε →
      Probability (fun g => uniform g + δ * (p g - q g)) ∧
      Match A (fun g => uniform g + δ * (p g - q g)) uniform ∧
      TV (fun g => (uniform g + δ * (p g - q g)) - uniform g) = δ ∧
      (uniform i + δ * (p i - q i)) - uniform i = (p i - q i) * δ := by
  have hv := kernel_of_match A p q hp hq hm
  obtain ⟨ε, hε, hprob, _⟩ := kernel_small_perturbation A _ hv
  have htv := optimal_pair_tv_one A i p q hp hq hm hpos hb
  refine ⟨ε, hε, fun δ hδ hle => ⟨
    probability_perturbation_smaller _ ε δ hδ hle hprob hv.1,
    perturbation_match A _ hv δ, ?_, ?_⟩⟩
  · simp only [add_sub_cancel_left, tv_smul, abs_of_nonneg hδ, htv, mul_one]
  · ring

end
end OrbitalMarginals
