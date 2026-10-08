import BapatSelectorRows

set_option autoImplicit false
open BapatFiniteRank BapatRankTwo.MarkedInversions
open scoped ComplexConjugate

namespace BapatRealExistence
noncomputable section

/-- Any real homogeneous observable has equal norm on conjugate phase orbits. -/
theorem norm_complexEval_eq_on_conjugate_orbits (p : MvPolynomial (Fin 4) ℝ) (d : ℕ)
    (hp : p.IsHomogeneous d) (u z : EuclideanSpace ℂ (Fin 4))
    (h : ∃ a : ℂ, ‖a‖=1 ∧ (z=a • u ∨ z=a • conjugateComplex4 u)) :
    ‖complexEval p z‖ = ‖complexEval p u‖ := by
  obtain ⟨a,ha,h|h⟩ := h
  · rw [h,norm_complexEval_phase p d hp a ha]
  · rw [h,norm_complexEval_phase p d hp a ha,complexEval_conjugate,RCLike.norm_conj]

theorem rowWedgeEnergy_eq_on_conjugate_orbits {n : ℕ} (v : Fin n → Fin 4 → ℝ)
    (u z : ComplexUnitSphere4)
    (h : ∃ a : ℂ, ‖a‖=1 ∧
      ((z : EuclideanSpace ℂ (Fin 4))=a • (u : EuclideanSpace ℂ (Fin 4)) ∨
       (z : EuclideanSpace ℂ (Fin 4))=a • conjugateComplex4 u)) :
    rowWedgeEnergy v z = rowWedgeEnergy v u := by
  unfold rowWedgeEnergy
  apply Finset.sum_congr rfl
  intro pair hp
  rw [norm_complexEval_eq_on_conjugate_orbits _ _
    (wedgePolynomial_isHomogeneous v pair.1 pair.2) u z h]

/-- Appending the four selector rows retains a positive chosen canonical maximum
and forces every augmented maximum into its two conjugate phase orbits. -/
theorem appendSelectorRows_peak {n : ℕ} (v : Fin n → Fin 4 → ℝ)
    {t : ℝ} (ht : 1/2 ≤ t) (ht' : t < 3/4)
    (hpos : 0 < ‖complexEval (formsProduct v) (canonicalComplex4 t)‖)
    (hmax : ∀ z : ComplexUnitSphere4,
      rowProductModulus v z ≤ ‖complexEval (formsProduct v) (canonicalComplex4 t)‖) :
    let u := canonicalSphere4 t (by linarith) (by linarith)
    let w := appendSelectorRows v (selectorParameter t)
    0 < rowProductModulus w u ∧
    (∀ z, rowProductModulus w z ≤ rowProductModulus w u) ∧
    (∀ z, rowProductModulus w z = rowProductModulus w u →
      ∃ a : ℂ, ‖a‖=1 ∧
        ((z : EuclideanSpace ℂ (Fin 4))=a • canonicalComplex4 t ∨
         (z : EuclideanSpace ℂ (Fin 4))=a • conjugateComplex4 (canonicalComplex4 t))) := by
  dsimp only
  let u := canonicalSphere4 t (show 0 ≤ t by linarith) (show t ≤ 1 by linarith)
  let c := selectorParameter t
  let w := appendSelectorRows v c
  have hc : 0 ≤ c := selectorParameter_nonneg ht ht'
  have hu : ‖selectorQuartic c (canonicalComplex4 t)‖^2 = selectorProfile c t :=
    selectorQuartic_canonical_attains (by linarith) (by linarith) c
  have huPos : 0 < ‖selectorQuartic c (canonicalComplex4 t)‖ := by
    have h := selectorProfile_max_pos ht ht'
    rw [← hu] at h
    nlinarith [norm_nonneg (selectorQuartic c (canonicalComplex4 t))]
  have hH (z : ComplexUnitSphere4) :
      ‖selectorQuartic c z‖ ≤ ‖selectorQuartic c (canonicalComplex4 t)‖ := by
    have hz := selectorQuartic_bound ht ht' z
    rw [← hu] at hz
    nlinarith [norm_nonneg (selectorQuartic c z),norm_nonneg (selectorQuartic c (canonicalComplex4 t))]
  have hproduct (z : ComplexUnitSphere4) : rowProductModulus w z =
      rowProductModulus v z * ‖selectorQuartic c z‖ := by
    unfold rowProductModulus w
    rw [appendSelectorRows_product v hc,norm_mul]
  have huprod : rowProductModulus w u =
      ‖complexEval (formsProduct v) (canonicalComplex4 t)‖ *
        ‖selectorQuartic c (canonicalComplex4 t)‖ := hproduct u
  refine ⟨?_,?_,?_⟩
  · change 0 < rowProductModulus w u
    rw [huprod]
    exact mul_pos hpos huPos
  · intro z
    change rowProductModulus w z ≤ rowProductModulus w u
    rw [hproduct,huprod]
    exact mul_le_mul (hmax z) (hH z) (norm_nonneg _) (norm_nonneg _)
  · intro z hz
    change rowProductModulus w z = rowProductModulus w u at hz
    have he : ‖selectorQuartic c z‖ = ‖selectorQuartic c (canonicalComplex4 t)‖ := by
      apply le_antisymm (hH z)
      apply le_of_not_gt
      intro hlt
      have hlt' : rowProductModulus w z < rowProductModulus w u := by
        rw [hproduct,huprod]
        exact (mul_le_mul_of_nonneg_right (hmax z) (norm_nonneg _)).trans_lt
          (mul_lt_mul_of_pos_left hlt hpos)
      exact hlt'.ne hz
    exact selectorQuartic_equality_phase_orbits ht ht' z (by rw [he]; exact hu)

/-- This closes the common-peak observable premise once the base's canonical
maximum and its strict ordered wedge gap have been supplied. -/
theorem selected_base_negative_endpoint {n : ℕ} (v : Fin n → Fin 4 → ℝ)
    {t : ℝ} (ht : 1/2 ≤ t) (ht' : t < 3/4)
    (hpos : 0 < ‖complexEval (formsProduct v) (canonicalComplex4 t)‖)
    (hmax : ∀ z : ComplexUnitSphere4,
      rowProductModulus v z ≤ ‖complexEval (formsProduct v) (canonicalComplex4 t)‖)
    (hgap : let u := canonicalSphere4 t (by linarith) (by linarith)
      let w := appendSelectorRows v (selectorParameter t)
      ((n+4 : ℕ) : ℝ)^4 * (rowProductModulus w u)^2 < 2 * rowWedgeEnergy w u) :
    ∃ L : ℕ, 0 < L ∧ 4 < (n+4)*L ∧
      (qPolynomial (gram (contiguousRows (appendSelectorRows v (selectorParameter t)) L))).derivative.eval 1 < 0 := by
  obtain ⟨hp,hm,ho⟩ := appendSelectorRows_peak v ht ht' hpos hmax
  apply exists_contiguous_negative_endpoint _ (by omega) _ hp hm _ hgap
  intro z hz
  exact rowWedgeEnergy_eq_on_conjugate_orbits _ _ z (ho z hz)

end
end BapatRealExistence
