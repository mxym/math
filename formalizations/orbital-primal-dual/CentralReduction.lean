import GroupAction

open scoped BigOperators

namespace OrbitalMarginals

noncomputable section

variable {G Ω : Type*} [Group G] [Fintype G] [Fintype Ω] [DecidableEq Ω]
  [MulAction G Ω]

def conjugationEquiv (h : G) : G ≃ G where
  toFun g := h * g * h⁻¹
  invFun g := h⁻¹ * g * h
  left_inv g := by group
  right_inv g := by group

def conjugate (h : G) (v : G → ℝ) (g : G) : ℝ := v (h * g * h⁻¹)

def centralAverage (v : G → ℝ) (g : G) : ℝ :=
  (∑ h, conjugate h v g) / (Fintype.card G : ℝ)

def Central (v : G → ℝ) : Prop := ∀ h g, v (h * g * h⁻¹) = v g

theorem sum_conjugate (h : G) (v : G → ℝ) : (∑ g, conjugate h v g) = ∑ g, v g := by
  simpa [conjugate, conjugationEquiv] using Equiv.sum_comp (conjugationEquiv h) v

omit [Fintype G] [Fintype Ω] in
theorem imageFeature_conjugate (h g : G) (x y : Ω) :
    imageFeatures (x, y) g = imageFeatures (h • x, h • y) (h * g * h⁻¹) := by
  simp [imageFeatures, mul_smul, smul_left_cancel_iff]

omit [Fintype Ω] in
theorem kernel_conjugate (h : G) (v : G → ℝ) (hv : Kernel (imageFeatures (G := G) (Ω := Ω)) v) :
    Kernel (imageFeatures (G := G) (Ω := Ω)) (conjugate h v) := by
  constructor
  · exact (sum_conjugate h v).trans hv.1
  · rintro ⟨x, y⟩
    calc
      (∑ g, imageFeatures (x, y) g * conjugate h v g) =
          ∑ g, imageFeatures (h • x, h • y) (h * g * h⁻¹) * v (h * g * h⁻¹) := by
        apply Finset.sum_congr rfl
        intro g _
        rw [imageFeature_conjugate h g x y]
        rfl
      _ = ∑ g, imageFeatures (h • x, h • y) g * v g := by
        simpa [conjugationEquiv] using Equiv.sum_comp (conjugationEquiv h)
          (fun g => imageFeatures (h • x, h • y) g * v g)
      _ = 0 := hv.2 (h • x, h • y)

theorem centralAverage_one (v : G → ℝ) : centralAverage v 1 = v 1 := by
  have hc : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [centralAverage, conjugate, hc]

theorem centralAverage_central (v : G → ℝ) : Central (centralAverage v) := by
  intro s g
  dsimp [centralAverage, conjugate]
  congr 1
  calc
    (∑ h, v (h * (s * g * s⁻¹) * h⁻¹)) =
        ∑ h, v ((h * s) * g * (h * s)⁻¹) := by
      apply Finset.sum_congr rfl
      intro h _
      apply congrArg v
      group
    _ = ∑ h, v (h * g * h⁻¹) := by
      simpa using Equiv.sum_comp (Equiv.mulRight s) (fun h => v (h * g * h⁻¹))

theorem centralAverage_probability (p : G → ℝ) (hp : Probability p) :
    Probability (centralAverage p) := by
  have hc : 0 < (Fintype.card G : ℝ) := by exact_mod_cast Fintype.card_pos
  constructor
  · intro g
    exact div_nonneg (Finset.sum_nonneg fun h _ => hp.1 _) hc.le
  · dsimp [centralAverage]
    rw [← Finset.sum_div, Finset.sum_comm]
    simp_rw [sum_conjugate, hp.2]
    simp [hc.ne']

theorem centralAverage_kernel (v : G → ℝ) (hv : Kernel (imageFeatures (G := G) (Ω := Ω)) v) :
    Kernel (imageFeatures (G := G) (Ω := Ω)) (centralAverage v) := by
  constructor
  · dsimp [centralAverage]
    rw [← Finset.sum_div, Finset.sum_comm]
    simp_rw [sum_conjugate, hv.1]
    simp
  · intro xy
    dsimp [centralAverage]
    simp only [← mul_div_assoc, Finset.mul_sum, ← Finset.sum_div]
    rw [Finset.sum_comm]
    have hh : ∀ h, (∑ g, imageFeatures xy g * conjugate h v g) = 0 :=
      fun h => (kernel_conjugate h v hv).2 xy
    simp_rw [hh]
    simp

theorem centralAverage_sub (p q : G → ℝ) :
    centralAverage (fun g => p g - q g) = fun g => centralAverage p g - centralAverage q g := by
  funext g
  simp [centralAverage, conjugate, Finset.sum_sub_distrib, sub_div]

omit [Fintype Ω] in
theorem match_of_difference_kernel (p q : G → ℝ)
    (h : Kernel (imageFeatures (G := G) (Ω := Ω)) (fun g => p g - q g)) : Match (imageFeatures (G := G) (Ω := Ω)) p q := by
  intro xy
  apply sub_eq_zero.mp
  simpa only [mul_sub, Finset.sum_sub_distrib] using h.2 xy

theorem centralAverage_match (p q : G → ℝ) (hp : Probability p) (hq : Probability q)
    (hm : Match (imageFeatures (G := G) (Ω := Ω)) p q) : Match (imageFeatures (G := G) (Ω := Ω)) (centralAverage p) (centralAverage q) := by
  apply match_of_difference_kernel
  rw [← centralAverage_sub]
  exact centralAverage_kernel _ (kernel_of_match (imageFeatures (G := G) (Ω := Ω)) p q hp hq hm)

theorem group_action_central_primal :
    ∃ p q : G → ℝ, ∃ coeff : Ω × Ω → ℝ,
      Probability p ∧ Probability q ∧ Central p ∧ Central q ∧
      (∀ x y : Ω, imageMass p x y = imageMass q x y) ∧
      p 1 - q 1 = oscillation (imageFeatures (G := G) (Ω := Ω)) (1 : G) coeff ∧
      PairBound (imageFeatures (G := G) (Ω := Ω)) (1 : G) (p 1 - q 1) ∧
      ∀ otherCoeff : Ω × Ω → ℝ, p 1 - q 1 ≤ oscillation (imageFeatures (G := G) (Ω := Ω)) (1 : G) otherCoeff := by
  obtain ⟨p, q, coeff, hp, hq, hm, ho, hb, _, hmin⟩ :=
    exact_oscillation_duality (imageFeatures (G := G) (Ω := Ω)) (1 : G)
  refine ⟨centralAverage p, centralAverage q, coeff,
    centralAverage_probability p hp, centralAverage_probability q hq,
    centralAverage_central p, centralAverage_central q,
    (match_iff_imageMass _ _).mp (centralAverage_match p q hp hq hm), ?_, ?_, ?_⟩
  · simpa only [centralAverage_one] using ho
  · simpa only [centralAverage_one] using hb
  · simpa only [centralAverage_one] using hmin

end
end OrbitalMarginals
