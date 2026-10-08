import Entry005.TruncationVolume
import Entry005.FacetRadialMass
import Entry005.TruncationGeometry
import Entry005.ProjectionVolumeSqueeze
import Entry005.PyramidContinuity

noncomputable section
open MeasureTheory Metric Module
open scoped BigOperators RealInnerProductSpace Pointwise

namespace Entry005

abbrev TruncationFacetIndex (d : ℕ) := Fin d ⊕ Bool

def truncationDiagonal (d : ℕ) : Space d := WithLp.toLp 2 (fun _ => (1 : ℝ))

def truncationUnitDiagonal (d : ℕ) : Space d :=
  (Real.sqrt (d : ℝ))⁻¹ • truncationDiagonal d

def truncationFacetNormal (d : ℕ) : TruncationFacetIndex d → Space d
  | Sum.inl i => -truncationVertex i
  | Sum.inr false => truncationUnitDiagonal d
  | Sum.inr true => -truncationUnitDiagonal d

def truncationFacetHeight (d : ℕ) (t : ℝ) : TruncationFacetIndex d → ℝ
  | Sum.inl _ => 0
  | Sum.inr false => (Real.sqrt (d : ℝ))⁻¹
  | Sum.inr true => -t / Real.sqrt (d : ℝ)

theorem truncation_diagonal_inner (d : ℕ) (x : Space d) :
    inner ℝ (truncationDiagonal d) x = ∑ i, x i := by
  simp [truncationDiagonal, PiLp.inner_apply, RCLike.inner_apply]

theorem truncation_unit_diagonal_inner (d : ℕ) (x : Space d) :
    inner ℝ (truncationUnitDiagonal d) x =
      (Real.sqrt (d : ℝ))⁻¹ * ∑ i, x i := by
  rw [truncationUnitDiagonal, real_inner_smul_left, truncation_diagonal_inner]

theorem truncation_unit_diagonal_norm {d : ℕ} (hd : 0 < d) :
    ‖truncationUnitDiagonal d‖ = 1 := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hs := Real.sqrt_pos.mpr hdR
  rw [truncationUnitDiagonal, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hs)]
  have hdiag : ‖truncationDiagonal d‖ = Real.sqrt (d : ℝ) := by
    simp [EuclideanSpace.norm_eq, truncationDiagonal]
  rw [hdiag, inv_mul_cancel₀ hs.ne']

theorem truncation_facet_norm {d : ℕ} (hd : 0 < d) (i : TruncationFacetIndex d) :
    ‖truncationFacetNormal d i‖ = 1 := by
  cases i with
  | inl i => simp [truncationFacetNormal, truncationVertex]
  | inr i => cases i <;> simp [truncationFacetNormal, truncation_unit_diagonal_norm hd]

theorem truncation_halfspace_representation {d : ℕ} (hd : 0 < d) (t : ℝ) :
    finiteHalfspaceSet (truncationFacetNormal d) (truncationFacetHeight d t) =
      truncationSet d t := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hs := Real.sqrt_pos.mpr hdR
  have hi : 0 < (Real.sqrt (d : ℝ))⁻¹ := inv_pos.mpr hs
  ext x
  constructor
  · intro hx
    refine ⟨?_, ?_, ?_⟩
    · intro i
      have hh := hx (Sum.inl i)
      simpa [truncationFacetNormal, truncationFacetHeight, truncationVertex,
        inner_neg_left, PiLp.inner_apply, RCLike.inner_apply] using hh
    · have hh := hx (Sum.inr true)
      simp only [truncationFacetNormal, truncationFacetHeight, inner_neg_left,
        truncation_unit_diagonal_inner, div_eq_mul_inv] at hh
      nlinarith
    · have hh := hx (Sum.inr false)
      simp only [truncationFacetNormal, truncationFacetHeight,
        truncation_unit_diagonal_inner] at hh
      nlinarith
  · rintro ⟨hx, ht, h1⟩ i
    cases i with
    | inl i =>
      simpa [truncationFacetNormal, truncationFacetHeight, truncationVertex,
        inner_neg_left, PiLp.inner_apply, RCLike.inner_apply] using hx i
    | inr i =>
      cases i
      · simpa only [truncationFacetNormal, truncationFacetHeight,
          truncation_unit_diagonal_inner, mul_one] using mul_le_mul_of_nonneg_left h1 hi.le
      · simp only [truncationFacetNormal, truncationFacetHeight, inner_neg_left,
          truncation_unit_diagonal_inner, div_eq_mul_inv]
        nlinarith

theorem truncation_top_facet {d : ℕ} (hd : 0 < d) (t : ℝ) (ht1 : t ≤ 1) :
    finiteHalfspaceFacet (truncationFacetNormal d) (truncationFacetHeight d t)
      (Sum.inr false) = {x : Space d | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1} := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hi : (Real.sqrt (d : ℝ))⁻¹ ≠ 0 := inv_ne_zero (Real.sqrt_pos.mpr hdR).ne'
  ext x
  simp only [finiteHalfspaceFacet, truncation_halfspace_representation hd t,
    Set.mem_inter_iff, Set.mem_ofPred_eq, truncationFacetNormal, truncationFacetHeight,
    truncation_unit_diagonal_inner]
  constructor
  · rintro ⟨hx, he⟩
    refine ⟨hx.1, ?_⟩
    exact mul_left_cancel₀ hi (by simpa only [mul_one] using he)
  · rintro ⟨hx, he⟩
    exact ⟨⟨hx, by simpa only [he] using ht1, by simp [he]⟩, by simp [he]⟩

theorem truncation_bottom_facet {d : ℕ} (hd : 0 < d) (t : ℝ) (ht1 : t ≤ 1) :
    finiteHalfspaceFacet (truncationFacetNormal d) (truncationFacetHeight d t)
      (Sum.inr true) = {x : Space d | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = t} := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hi : (Real.sqrt (d : ℝ))⁻¹ ≠ 0 := inv_ne_zero (Real.sqrt_pos.mpr hdR).ne'
  ext x
  simp only [finiteHalfspaceFacet, truncation_halfspace_representation hd t,
    Set.mem_inter_iff, Set.mem_ofPred_eq, truncationFacetNormal, truncationFacetHeight,
    inner_neg_left, truncation_unit_diagonal_inner, div_eq_mul_inv]
  constructor
  · rintro ⟨hx, he⟩
    refine ⟨hx.1, ?_⟩
    apply mul_left_cancel₀ hi
    nlinarith [he]
  · rintro ⟨hx, he⟩
    exact ⟨⟨hx, by simp [he], by simpa only [he] using ht1⟩, by rw [he]; ring⟩

/-- The radial cone over the actual top facet is the actual ambient simplex,
even though the truncated body itself does not contain the origin. -/
theorem truncation_top_facet_cone {d : ℕ} (hd : 0 < d) (t : ℝ) (ht1 : t ≤ 1) :
    finiteHalfspaceFacetCone (truncationFacetNormal d) (truncationFacetHeight d t)
      (Sum.inr false) = truncationAmbientSimplex d 1 := by
  ext x
  constructor
  · rintro ⟨s, hs, q, hq, rfl⟩
    rw [truncation_top_facet hd t ht1] at hq
    refine ⟨fun i => ?_, ?_⟩
    · change 0 ≤ s * q i
      exact mul_nonneg hs.1 (hq.1 i)
    · change (∑ i, s * q i) ≤ 1
      simpa only [← Finset.mul_sum, hq.2, mul_one] using hs.2
  · rintro ⟨hx, hsum⟩
    let s := ∑ i, x i
    have hs0 : 0 ≤ s := Finset.sum_nonneg (fun i _ => hx i)
    by_cases hs : s = 0
    · have hx0 : x = 0 := by
        ext i
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hx i)).mp hs
        simpa using this i (Finset.mem_univ i)
      refine ⟨0, by simp, truncationVertex ⟨0, hd⟩, ?_, ?_⟩
      · rw [truncation_top_facet hd t ht1]
        exact ⟨fun i => by simp only [truncationVertex_apply]; split_ifs <;> norm_num,
          truncationVertex_sum _⟩
      · simp [hx0]
    · have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
      refine ⟨s, ⟨hs0, hsum⟩, s⁻¹ • x, ?_, ?_⟩
      · rw [truncation_top_facet hd t ht1]
        refine ⟨fun i => ?_, ?_⟩
        · change 0 ≤ s⁻¹ * x i
          exact mul_nonneg (inv_nonneg.mpr hs0) (hx i)
        · change (∑ i, s⁻¹ * x i) = 1
          rw [← Finset.mul_sum, inv_mul_cancel₀ hs]
      · rw [smul_smul, mul_inv_cancel₀ hs, one_smul]

/-- Intrinsic area of the actual top facet, deduced from its actual cone
and the kernel-checked radial Fubini identity rather than an area assumption. -/
theorem truncation_top_facet_area {d : ℕ} (hd : 0 < d) (t : ℝ)
    (ht0 : 0 < t) (ht1 : t < 1) :
    finiteHalfspaceFacetArea (truncationFacetNormal d) (truncationFacetHeight d t)
      (Sum.inr false) = Real.sqrt (d : ℝ) / ((d - 1).factorial : ℝ) := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hs := Real.sqrt_pos.mpr hdR
  have hc : IsCompact (finiteHalfspaceSet (truncationFacetNormal d)
      (truncationFacetHeight d t)) := by
    rw [truncation_halfspace_representation hd t]
    exact truncationSet_isCompact ht0 ht1
  have hv := finite_halfspace_facet_cone_volume (truncationFacetNormal d)
    (truncationFacetHeight d t) (Sum.inr false) (truncation_facet_norm hd _)
    (inv_pos.mpr hs) hc
  rw [truncation_top_facet_cone hd t ht1.le,
    truncation_ambient_simplex_real_volume d 1 zero_le_one, one_pow] at hv
  simp only [truncationFacetHeight, Space, finrank_euclideanSpace, Fintype.card_fin] at hv
  have hf : (d.factorial : ℝ) = (d : ℝ) * ((d - 1).factorial : ℝ) := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
    simp [Nat.factorial_succ]
  rw [hf] at hv
  have hp : (((d - 1).factorial : ℝ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (d - 1)
  field_simp [hdR.ne', hs.ne', hp] at hv ⊢
  nlinarith

theorem truncation_bottom_facet_homothety {d : ℕ} (hd : 0 < d) (t : ℝ)
    (ht0 : 0 < t) (ht1 : t ≤ 1) :
    finiteHalfspaceFacet (truncationFacetNormal d) (truncationFacetHeight d t)
      (Sum.inr true) =
      t • finiteHalfspaceFacet (truncationFacetNormal d) (truncationFacetHeight d t)
        (Sum.inr false) := by
  rw [truncation_bottom_facet hd t ht1, truncation_top_facet hd t ht1]
  ext x
  constructor
  · rintro ⟨hx, hs⟩
    refine ⟨t⁻¹ • x, ⟨fun i => ?_, ?_⟩, ?_⟩
    · change 0 ≤ t⁻¹ * x i
      exact mul_nonneg (inv_nonneg.mpr ht0.le) (hx i)
    · change (∑ i, t⁻¹ * x i) = 1
      rw [← Finset.mul_sum, hs, inv_mul_cancel₀ ht0.ne']
    · change t • (t⁻¹ • x) = x
      rw [smul_smul, mul_inv_cancel₀ ht0.ne', one_smul]
  · rintro ⟨q, ⟨hq, hs⟩, rfl⟩
    refine ⟨fun i => ?_, ?_⟩
    · change 0 ≤ t * q i
      exact mul_nonneg ht0.le (hq i)
    · change (∑ i, t * q i) = t
      rw [← Finset.mul_sum, hs, mul_one]

/-- The actual bottom intrinsic facet area scales by the tangent dimension.
Opposite outward normals describe exactly the same Euclidean tangent space. -/
theorem truncation_facet_area_projection {d : ℕ} (hd : 0 < d) (t : ℝ)
    (i : TruncationFacetIndex d) :
    finiteHalfspaceFacetArea (truncationFacetNormal d) (truncationFacetHeight d t) i =
      projectionVolumeSet
        (finiteHalfspaceFacet (truncationFacetNormal d) (truncationFacetHeight d t) i)
        (truncationFacetNormal d i) := by
  unfold finiteHalfspaceFacetArea projectionVolumeSet
  rw [finite_halfspace_facet_chart_projection_image (truncationFacetNormal d)
    (truncationFacetHeight d t) i (truncation_facet_norm hd i)]

theorem truncation_bottom_facet_area {d : ℕ} (hd : 0 < d) (t : ℝ)
    (ht0 : 0 < t) (ht1 : t < 1) :
    finiteHalfspaceFacetArea (truncationFacetNormal d) (truncationFacetHeight d t)
      (Sum.inr true) =
      t ^ (d - 1) * (Real.sqrt (d : ℝ) / ((d - 1).factorial : ℝ)) := by
  rw [truncation_facet_area_projection hd t (Sum.inr true), truncationFacetNormal,
    projectionVolumeSet_neg_normal, truncation_bottom_facet_homothety hd t ht0 ht1.le,
    projection_volume_nonnegative_smul _ _ (truncation_unit_diagonal_norm hd) t ht0.le]
  simp only [Space, finrank_euclideanSpace, Fintype.card_fin]
  have htop := truncation_facet_area_projection hd t (Sum.inr false)
  simp only [truncationFacetNormal] at htop
  rw [← htop, truncation_top_facet_area hd t ht0 ht1]

end Entry005
