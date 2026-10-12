import Entry005.SimplexVolumeInterface
import Mxym.StochasticRigidity
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.Abel

noncomputable section
open MeasureTheory MeasureTheory.Measure Metric
open scoped BigOperators Pointwise

namespace Entry005

/-- Actual vertex matching from genuine volume ratio; the center is arbitrary. -/
theorem simplex_vertex_matching {d : ℕ} (hd : 1 ≤ d)
    (P S : Affine.Simplex ℝ (Space d) d) (c : Space d) (M δ : ℝ)
    (hsubset : simplexSet S ⊆ simplexSet P)
    (hbound : ∀ i, ‖P.points i - c‖ ≤ M)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 8)
    (hratio : 1 - δ ≤ (volume (simplexSet S)).toReal / (volume (simplexSet P)).toReal) :
    ∃ σ : Equiv.Perm (Fin (d + 1)), ∀ j, ‖S.points j - P.points (σ j)‖ ≤ 2 * M * δ := by
  classical
  have h := simplexMatrixVolumeInterface d hd P S hsubset
  obtain ⟨_, _, _, _, hnonneg, hsum, hreconstruct, hdet⟩ := h
  obtain ⟨σ, hσ⟩ := Mxym.StochasticRigidity.near_permutation_sharp
    (simplexBarycentricMatrix P S) hnonneg hsum δ hδ0 hδ (hdet ▸ hratio)
  have hM : 0 ≤ M := (norm_nonneg _).trans (hbound 0)
  refine ⟨σ, fun j => ?_⟩
  have hshift : (∑ i, simplexBarycentricMatrix P S i j • (P.points i - c)) = S.points j - c := by
    simp_rw [smul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul, hsum, one_smul, hreconstruct]
  have he : (∑ i, (simplexBarycentricMatrix P S i j - if i = σ j then 1 else 0) •
      (P.points i - c)) = S.points j - P.points (σ j) := by
    simp_rw [sub_smul]
    rw [Finset.sum_sub_distrib, hshift]
    simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    abel
  rw [← he]
  calc
    _ ≤ ∑ i, ‖(simplexBarycentricMatrix P S i j - if i = σ j then 1 else 0) •
        (P.points i - c)‖ := norm_sum_le _ _
    _ = ∑ i, |simplexBarycentricMatrix P S i j - if i = σ j then 1 else 0| *
        ‖P.points i - c‖ := by simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ i, |simplexBarycentricMatrix P S i j - if i = σ j then 1 else 0| * M := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hbound i) (abs_nonneg _)
    _ = (∑ i, |simplexBarycentricMatrix P S i j - if i = σ j then 1 else 0|) * M :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ 2 * M * δ := by
      have ht := mul_le_mul_of_nonneg_right (hσ j).2 hM
      nlinarith

/-- Exact volume endpoint identifies actual vertices and convex hulls without normalization. -/
theorem simplex_equal_volume_permutation {d : ℕ} (hd : 1 ≤ d)
    (P S : Affine.Simplex ℝ (Space d) d) (hsubset : simplexSet S ⊆ simplexSet P)
    (hratio : 1 ≤ (volume (simplexSet S)).toReal / (volume (simplexSet P)).toReal) :
    ∃ σ : Equiv.Perm (Fin (d + 1)),
      (∀ j, S.points j = P.points (σ j)) ∧ simplexSet S = simplexSet P := by
  classical
  obtain ⟨_, _, _, _, hnonneg, hsum, hreconstruct, hdet⟩ :=
    simplexMatrixVolumeInterface d hd P S hsubset
  obtain ⟨σ, hσ⟩ := Mxym.StochasticRigidity.exact_permutation
    (simplexBarycentricMatrix P S) hnonneg hsum (hdet ▸ hratio)
  have hv : ∀ j, S.points j = P.points (σ j) := by
    intro j
    have hj := hreconstruct j
    simp_rw [hσ] at hj
    simpa only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true] using hj.symm
  refine ⟨σ, hv, ?_⟩
  apply congrArg (convexHull ℝ)
  ext x
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨σ j, (hv j).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨σ.symm i, by simpa using hv (σ.symm i)⟩

private theorem nearby_mem_homothety {d : ℕ} {A : Set (Space d)}
    (hconv : Convex ℝ A) (c x y : Space d) (r : ℝ)
    (hr : 0 ≤ r) (hball : closedBall c 1 ⊆ A) (hy : y ∈ A)
    (hdist : ‖x - y‖ ≤ r) : x ∈ AffineMap.homothety c (1 + r) '' A := by
  by_cases hr0 : r = 0
  · have he : x = y := sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (hr0 ▸ hdist) (norm_nonneg _)))
    simpa [hr0, he] using hy
  have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  let u := c + r⁻¹ • (x - y)
  have hu : u ∈ A := by
    apply hball
    rw [mem_closedBall, dist_eq_norm]
    have hh : ‖u - c‖ ≤ 1 := by
      dsimp [u]
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hr)]
      calc
        _ ≤ r⁻¹ * r := mul_le_mul_of_nonneg_left hdist (inv_nonneg.mpr hr)
        _ = 1 := inv_mul_cancel₀ hr0
    exact hh
  obtain ⟨z, hz, he⟩ := hconv.exists_mem_add_smul_eq hy hu zero_le_one hr
  refine ⟨z, hz, ?_⟩
  simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, smul_sub]
  rw [he, one_smul]
  dsimp [u]
  rw [smul_add, smul_smul, mul_inv_cancel₀ hr0, one_smul, add_smul, one_smul]
  abel

/-- Hull conversion about an explicitly supplied center; no centroid is inferred. -/
theorem simplex_hull_matching {d : ℕ} (hd : 1 ≤ d)
    (P S : Affine.Simplex ℝ (Space d) d) (c : Space d) (M δ : ℝ)
    (hsubset : simplexSet S ⊆ simplexSet P)
    (hbound : ∀ i, ‖P.points i - c‖ ≤ M) (hball : closedBall c 1 ⊆ simplexSet S)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 8)
    (hratio : 1 - δ ≤ (volume (simplexSet S)).toReal / (volume (simplexSet P)).toReal) :
    simplexSet P ⊆ AffineMap.homothety c (1 + 2 * M * δ) '' simplexSet S := by
  classical
  obtain ⟨σ, hσ⟩ := simplex_vertex_matching hd P S c M δ hsubset hbound hδ0 hδ hratio
  have hM : 0 ≤ M := (norm_nonneg _).trans (hbound 0)
  apply convexHull_min
  · rintro x ⟨i, rfl⟩
    have hy : S.points (σ.symm i) ∈ simplexSet S := subset_convexHull ℝ _ ⟨_, rfl⟩
    apply nearby_mem_homothety (convex_convexHull ℝ _) c _ _ (2 * M * δ)
      (by positivity) hball hy
    simpa only [σ.apply_symm_apply, norm_sub_rev] using hσ (σ.symm i)
  · exact Convex.affine_image _ (convex_convexHull ℝ _)

/-- The origin-normalized manuscript inclusion, with the stronger factor 2. -/
theorem simplex_hull_dilation {d : ℕ} (hd : 1 ≤ d)
    (P S : Affine.Simplex ℝ (Space d) d) (M δ : ℝ)
    (hsubset : simplexSet S ⊆ simplexSet P) (hbound : ∀ i, ‖P.points i‖ ≤ M)
    (hball : closedBall (0 : Space d) 1 ⊆ simplexSet S)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 8)
    (hratio : 1 - δ ≤ (volume (simplexSet S)).toReal / (volume (simplexSet P)).toReal) :
    simplexSet P ⊆ (1 + 2 * M * δ) • simplexSet S := by
  simpa only [sub_zero, AffineMap.coe_homothety, vsub_eq_sub, vadd_eq_add, add_zero,
    ← Set.image_smul] using simplex_hull_matching hd P S 0 M δ hsubset
      (by simpa using hbound) hball hδ0 hδ hratio

private theorem affine_image_volume {d : ℕ} (f : Space d →ᵃ[ℝ] Space d) (s : Set (Space d)) :
    volume (f '' s) = ENNReal.ofReal |LinearMap.det f.linear| * volume s := by
  have himage : f '' s = (fun x : Space d => x + -f 0) ⁻¹' (f.linear '' s) := by
    ext x
    change (∃ y ∈ s, f y = x) ↔ ∃ y ∈ s, f.linear y = x + -f 0
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y, hy, ?_⟩
      rw [congrFun f.decomp y]
      simp
    · rintro ⟨y, hy, he⟩
      refine ⟨y, hy, ?_⟩
      rw [congrFun f.decomp y, Pi.add_apply, he]
      simp
  rw [himage, measure_preimage_add_right]
  exact volume.addHaar_image_linearMap f.linear s

/-- Actual maximality applied to a genuinely shrunk enclosing simplex. -/
theorem maximum_simplex_volume_ratio {d : ℕ} (hd : 1 ≤ d)
    (K : ConvexBody (Space d)) (P S : Affine.Simplex ℝ (Space d) d)
    (c : Space d) (s : ℝ) (hmax : maximumInscribed K S)
    (_hs0 : 0 ≤ s) (hs1 : s < 1)
    (hshrink : AffineMap.homothety c (1 - s) '' simplexSet P ⊆ (K : Set (Space d))) :
    (1 - s) ^ d ≤ (volume (simplexSet S)).toReal / (volume (simplexSet P)).toReal ∧
    1 - (d : ℝ) * s ≤ (1 - s) ^ d ∧
    1 - (d : ℝ) * s ≤ (volume (simplexSet S)).toReal / (volume (simplexSet P)).toReal := by
  have hr : 0 < 1 - s := sub_pos.mpr hs1
  let f := AffineMap.homothety c (1 - s)
  let T := P.map f (AffineMap.homothety_injective c (ne_of_gt hr))
  have hT : simplexSet T = f '' simplexSet P := by
    change convexHull ℝ (Set.range (f ∘ P.points)) = f '' convexHull ℝ (Set.range P.points)
    rw [Set.range_comp, AffineMap.image_convexHull]
  have hmeasure := hmax.2 T (hT ▸ hshrink)
  have hscale : volume (simplexSet T) = ENNReal.ofReal ((1 - s) ^ d) * volume (simplexSet P) := by
    rw [hT, affine_image_volume]
    simp only [f, AffineMap.homothety_linear, LinearMap.det_smul, LinearMap.det_id, mul_one]
    simp [Space, abs_of_nonneg (pow_nonneg hr.le d)]
  have hSfinite := (simplexMatrixVolumeInterface d hd S S (Set.Subset.refl _)).2.2.1
  have hPpos := (simplexMatrixVolumeInterface d hd P P (Set.Subset.refl _)).2.2.2.1
  have hreal := ENNReal.toReal_mono hSfinite hmeasure
  rw [hscale, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr.le d)] at hreal
  have hratio := (le_div_iff₀ hPpos).mpr hreal
  have hbern : 1 - (d : ℝ) * s ≤ (1 - s) ^ d := by
    simpa only [sub_eq_add_neg, mul_neg] using
      one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ -s) d
  exact ⟨hratio, hbern, hbern.trans hratio⟩

/-- Every prescribed maximum simplex is retained about an explicit center. -/
theorem retain_maximum_simplex_about {d : ℕ} (hd : 1 ≤ d)
    (K : ConvexBody (Space d)) (P S : Affine.Simplex ℝ (Space d) d)
    (c : Space d) (M s : ℝ) (hmax : maximumInscribed K S)
    (hKP : (K : Set (Space d)) ⊆ simplexSet P)
    (hbound : ∀ i, ‖P.points i - c‖ ≤ M) (hball : closedBall c 1 ⊆ simplexSet S)
    (hs0 : 0 ≤ s) (hds : (d : ℝ) * s ≤ 1 / 8)
    (hshrink : AffineMap.homothety c (1 - s) '' simplexSet P ⊆ (K : Set (Space d))) :
    (K : Set (Space d)) ⊆ AffineMap.homothety c (1 + 2 * M * (d : ℝ) * s) '' simplexSet S := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hs1 : s < 1 := by nlinarith
  have hv := (maximum_simplex_volume_ratio hd K P S c s hmax hs0 hs1 hshrink).2.2
  have hi := simplex_hull_matching hd P S c M ((d : ℝ) * s)
    (hmax.1.trans hKP) hbound hball (by positivity) hds hv
  have he : 1 + 2 * M * ((d : ℝ) * s) = 1 + 2 * M * (d : ℝ) * s := by ring
  rw [he] at hi
  exact hKP.trans hi

/-- The original centroid is used literally, with centered geometric hypotheses. -/
theorem retain_maximum_simplex_centroid {d : ℕ} (hd : 1 ≤ d)
    (K : ConvexBody (Space d)) (P S : Affine.Simplex ℝ (Space d) d)
    (M s : ℝ) (hmax : maximumInscribed K S)
    (hKP : (K : Set (Space d)) ⊆ simplexSet P)
    (hbound : ∀ i, ‖P.points i - S.centroid‖ ≤ M)
    (hball : closedBall S.centroid 1 ⊆ simplexSet S)
    (hs0 : 0 ≤ s) (hds : (d : ℝ) * s ≤ 1 / 8)
    (hshrink : AffineMap.homothety S.centroid (1 - s) '' simplexSet P ⊆ (K : Set (Space d))) :
    (K : Set (Space d)) ⊆ centeredDilation S (2 * M * (d : ℝ) * s) := by
  simpa only [centeredDilation, AffineMap.coe_homothety, vsub_eq_sub, vadd_eq_add, add_comm] using
    retain_maximum_simplex_about hd K P S S.centroid M s hmax hKP hbound hball hs0 hds hshrink

/-- The genuine excess functional is bounded about the original prescribed centroid. -/
theorem retain_maximum_simplex_excess {d : ℕ} (hd : 1 ≤ d)
    (K : ConvexBody (Space d)) (P S : Affine.Simplex ℝ (Space d) d)
    (M s : ℝ) (hmax : maximumInscribed K S)
    (hKP : (K : Set (Space d)) ⊆ simplexSet P)
    (hbound : ∀ i, ‖P.points i - S.centroid‖ ≤ M)
    (hball : closedBall S.centroid 1 ⊆ simplexSet S)
    (hs0 : 0 ≤ s) (hds : (d : ℝ) * s ≤ 1 / 8)
    (hshrink : AffineMap.homothety S.centroid (1 - s) '' simplexSet P ⊆ (K : Set (Space d))) :
    excess (K : Set (Space d)) S ≤ 2 * M * (d : ℝ) * s := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hbound 0)
  unfold excess
  apply csInf_le
  · exact ⟨0, fun t ht => ht.1⟩
  · exact ⟨by positivity, retain_maximum_simplex_centroid hd K P S M s hmax hKP
      hbound hball hs0 hds hshrink⟩

/-- The manuscript's origin-normalized maximum-simplex inclusion, including s=0. -/
theorem retain_maximum_simplex {d : ℕ} (hd : 1 ≤ d)
    (K : ConvexBody (Space d)) (P S : Affine.Simplex ℝ (Space d) d)
    (M s : ℝ) (hmax : maximumInscribed K S)
    (hKP : (K : Set (Space d)) ⊆ simplexSet P)
    (hbound : ∀ i, ‖P.points i‖ ≤ M) (hball : closedBall (0 : Space d) 1 ⊆ simplexSet S)
    (hs0 : 0 ≤ s) (hds : (d : ℝ) * s ≤ 1 / 8)
    (hshrink : (1 - s) • simplexSet P ⊆ (K : Set (Space d))) :
    (K : Set (Space d)) ⊆ (1 + 2 * M * (d : ℝ) * s) • simplexSet S := by
  have hz (r : ℝ) : (AffineMap.homothety (0 : Space d) r : Space d → Space d) = (fun x => r • x) := by
    ext x
    simp [AffineMap.homothety_apply]
  have hh : AffineMap.homothety (0 : Space d) (1 - s) '' simplexSet P ⊆ (K : Set (Space d)) := by
    simpa only [hz, Set.image_smul] using hshrink
  simpa only [hz, Set.image_smul] using retain_maximum_simplex_about hd K P S 0 M s
    hmax hKP (by simpa only [sub_zero] using hbound) hball hs0 hds hh

end Entry005
