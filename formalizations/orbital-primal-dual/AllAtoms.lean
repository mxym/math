import UniversalOrbitalTheorem

open scoped BigOperators

namespace OrbitalMarginals

noncomputable section

variable {G Ω : Type*} [Group G] [Fintype G] [Fintype Ω] [DecidableEq Ω]
  [MulAction G Ω]

/-- Translation gives equality of the actual kernel-ratio sets, not just a
transported upper bound.  Therefore optimality holds at every atom. -/
theorem kernelRatios_all_atoms (σ : G) :
    kernelRatios (imageFeatures (G := G) (Ω := Ω)) σ =
      kernelRatios (imageFeatures (G := G) (Ω := Ω)) (1 : G) := by
  ext r
  constructor
  · rintro ⟨v, hv, hne, he⟩
    have htne : translate σ v ≠ 0 := by
      intro ht
      have hz : TV v = 0 := by rw [← tv_translate σ v, ht]; simp [TV]
      exact hne ((tv_eq_zero_iff v).mp hz)
    refine ⟨translate σ v, kernel_translate σ v hv, htne, ?_⟩
    simpa only [translate, mul_one, tv_translate] using he
  · rintro ⟨v, hv, hne, he⟩
    have htne : translate σ⁻¹ v ≠ 0 := by
      intro ht
      have hz : TV v = 0 := by rw [← tv_translate σ⁻¹ v, ht]; simp [TV]
      exact hne ((tv_eq_zero_iff v).mp hz)
    refine ⟨translate σ⁻¹ v, kernel_translate σ⁻¹ v hv, htne, ?_⟩
    simpa only [translate, inv_mul_cancel, tv_translate] using he

theorem sharpConstant_all_atoms (σ : G) :
    sharpConstant (imageFeatures (G := G) (Ω := Ω)) σ =
      sharpConstant (imageFeatures (G := G) (Ω := Ω)) (1 : G) := by
  simp only [sharpConstant, kernelRatios_all_atoms]

/-- Every normalized actual kernel vector produces a full interval of sharp
probability perturbations. -/
theorem normalized_kernel_attainment {I J : Type*} [Fintype I] [Nonempty I]
    (A : J → I → ℝ) (i : I) (v : I → ℝ) (C : ℝ)
    (hv : Kernel A v) (htv : TV v = 1) (hi : v i = C) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 ≤ δ → δ ≤ ε →
      Probability (fun g => uniform g + δ * v g) ∧
      Match A (fun g => uniform g + δ * v g) uniform ∧
      TV (fun g => (uniform g + δ * v g) - uniform g) = δ ∧
      (uniform i + δ * v i) - uniform i = C * δ := by
  obtain ⟨ε, hε, hprob, _⟩ := kernel_small_perturbation A v hv
  refine ⟨ε, hε, fun δ hδ hle => ⟨
    probability_perturbation_smaller v ε δ hδ hle hprob hv.1,
    perturbation_match A v hv δ, ?_, ?_⟩⟩
  · simp only [add_sub_cancel_left, tv_smul, abs_of_nonneg hδ, htv, mul_one]
  · rw [hi]
    ring

theorem sharp_attainment_all_atoms (p q : G → ℝ) (hp : Probability p) (hq : Probability q)
    (hm : Match (imageFeatures (G := G) (Ω := Ω)) p q)
    (hpos : 0 < p 1 - q 1)
    (hb : PairBound (imageFeatures (G := G) (Ω := Ω)) (1 : G) (p 1 - q 1)) :
    ∀ σ : G, ∃ v : G → ℝ, Kernel (imageFeatures (G := G) (Ω := Ω)) v ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 ≤ δ → δ ≤ ε →
        Probability (fun g => uniform g + δ * v g) ∧
        Match (imageFeatures (G := G) (Ω := Ω)) (fun g => uniform g + δ * v g) uniform ∧
        TV (fun g => (uniform g + δ * v g) - uniform g) = δ ∧
        (uniform σ + δ * v σ) - uniform σ = (p 1 - q 1) * δ := by
  intro σ
  let v := translate σ⁻¹ (fun g => p g - q g)
  have hv := kernel_translate σ⁻¹ _
    (kernel_of_match (imageFeatures (G := G) (Ω := Ω)) p q hp hq hm)
  have ht : TV v = 1 := by
    rw [tv_translate]
    exact optimal_pair_tv_one _ _ p q hp hq hm hpos hb
  have hi : v σ = p 1 - q 1 := by simp [v, translate]
  exact ⟨v, hv, normalized_kernel_attainment _ σ v _ hv ht hi⟩

end
end OrbitalMarginals
