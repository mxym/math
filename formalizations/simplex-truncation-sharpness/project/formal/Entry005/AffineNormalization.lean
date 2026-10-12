import Entry005.HausdorffRetention
import Mathlib.Analysis.Normed.Affine.AddTorsorBases

noncomputable section
open Metric MeasureTheory MeasureTheory.Measure
open scoped BigOperators Pointwise
namespace Entry005

private def fullBasis {d : ℕ} (S : Affine.Simplex ℝ (Space d) d) :
    AffineBasis (Fin (d + 1)) ℝ (Space d) :=
  ⟨S.points, S.independent, S.affineSpan_eq_top (by simp [Space])⟩

/-- A concrete genuine affine equivalence sends any full-dimensional simplex to any other. -/
def simplexAffineEquiv {d : ℕ} (S T : Affine.Simplex ℝ (Space d) d) :
    Space d ≃ᵃ[ℝ] Space d :=
  AffineEquiv.ofLinearEquiv
    (((fullBasis S).basisOf 0).equiv ((fullBasis T).basisOf 0) (Equiv.refl _))
    (S.points 0) (T.points 0)

theorem simplexAffineEquiv_points {d : ℕ} (S T : Affine.Simplex ℝ (Space d) d)
    (i : Fin (d + 1)) : simplexAffineEquiv S T (S.points i) = T.points i := by
  classical
  by_cases hi : i = 0
  · subst i
    simp [simplexAffineEquiv]
  · have h := Module.Basis.equiv_apply ((fullBasis S).basisOf 0)
      (⟨i, hi⟩ : {j : Fin (d + 1) // j ≠ 0}) ((fullBasis T).basisOf 0) (Equiv.refl _)
    simp only [AffineBasis.basisOf_apply, Equiv.refl_apply, vsub_eq_sub] at h
    change (((fullBasis S).basisOf 0).equiv ((fullBasis T).basisOf 0) (Equiv.refl _))
      (S.points i - S.points 0) = T.points i - T.points 0 at h
    change (((fullBasis S).basisOf 0).equiv ((fullBasis T).basisOf 0) (Equiv.refl _))
      (S.points i - S.points 0) + T.points 0 = T.points i
    rw [h, sub_add_cancel]

/-- The genuine image simplex with injectivity discharged by the equivalence. -/
def affineSimplex {d : ℕ} (f : Space d ≃ᵃ[ℝ] Space d)
    (S : Affine.Simplex ℝ (Space d) d) : Affine.Simplex ℝ (Space d) d :=
  S.map f.toAffineMap (fun _ _ h => f.injective h)

/-- Actual simplex carriers commute with affine equivalences. -/
theorem simplexSet_affine_map {d : ℕ} (S : Affine.Simplex ℝ (Space d) d)
    (f : Space d ≃ᵃ[ℝ] Space d) :
    simplexSet (affineSimplex f S) = f '' simplexSet S := by
  change convexHull ℝ (Set.range (f ∘ S.points)) = f '' convexHull ℝ (Set.range S.points)
  rw [Set.range_comp]
  exact (f.toAffineMap.image_convexHull _).symm

/-- The image convex body uses the actual affine image and its proved compactness. -/
def affineBody {d : ℕ} (f : Space d ≃ᵃ[ℝ] Space d) (K : ConvexBody (Space d)) :
    ConvexBody (Space d) where
  carrier := f '' (K : Set (Space d))
  convex' := K.convex.affine_image f.toAffineMap
  isCompact' := K.isCompact.image f.toAffineMap.continuous_of_finiteDimensional
  nonempty' := K.nonempty.image f

/-- Actual Haar volume of every set transforms by the genuine determinant. -/
theorem volume_affine_image {d : ℕ} (f : Space d ≃ᵃ[ℝ] Space d) (A : Set (Space d)) :
    volume (f '' A) = ENNReal.ofReal |LinearMap.det f.linear.toLinearMap| * volume A := by
  have himage : f '' A = (fun x : Space d => x + -f 0) ⁻¹' (f.linear '' A) := by
    ext x
    change (∃ y ∈ A, f y = x) ↔ ∃ y ∈ A, f.linear y = x + -f 0
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y, hy, ?_⟩
      change f.linear y = f.toAffineMap y + -f.toAffineMap 0
      rw [congrFun f.toAffineMap.decomp y]
      simp
    · rintro ⟨y, hy, he⟩
      refine ⟨y, hy, ?_⟩
      change f.toAffineMap y = x
      rw [congrFun f.toAffineMap.decomp y, Pi.add_apply]
      change f.linear y + f 0 = x
      rw [he]
      simp
  rw [himage, measure_preimage_add_right]
  exact volume.addHaar_image_linearMap f.linear.toLinearMap A

/-- Maximality is transported through actual volume scaling, in both directions. -/
theorem maximumInscribed_affine_iff {d : ℕ} (f : Space d ≃ᵃ[ℝ] Space d)
    (K : ConvexBody (Space d)) (S : Affine.Simplex ℝ (Space d) d) :
    maximumInscribed (affineBody f K) (affineSimplex f S) ↔
      maximumInscribed K S := by
  have hc0 : ENNReal.ofReal |LinearMap.det f.linear.toLinearMap| ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]
    exact abs_pos.mpr (f.linear.isUnit_det'.ne_zero)
  have hcf : ENNReal.ofReal |LinearMap.det f.linear.toLinearMap| ≠ ⊤ := ENNReal.ofReal_ne_top
  constructor
  · intro h
    refine ⟨?_, fun T hT => ?_⟩
    · intro x hx
      have hfx : f x ∈ simplexSet (affineSimplex f S) := by
        rw [simplexSet_affine_map]
        exact ⟨x, hx, rfl⟩
      have hh := h.1 hfx
      obtain ⟨y, hy, he⟩ := hh
      exact f.injective he ▸ hy
    · have hh := h.2 (affineSimplex f T)
        (by rw [simplexSet_affine_map]; exact Set.image_mono hT)
      rw [simplexSet_affine_map, simplexSet_affine_map, volume_affine_image, volume_affine_image] at hh
      exact (ENNReal.mul_le_mul_iff_right hc0 hcf).mp hh
  · intro h
    refine ⟨by rw [simplexSet_affine_map]; exact Set.image_mono h.1, fun T hT => ?_⟩
    let U := affineSimplex f.symm T
    have hU : simplexSet U ⊆ (K : Set (Space d)) := by
      rw [simplexSet_affine_map]
      rintro x ⟨y, hy, rfl⟩
      obtain ⟨z, hz, he⟩ := hT hy
      simpa only [← he, f.symm_apply_apply] using hz
    have hTU : simplexSet T = f '' simplexSet U := by
      rw [simplexSet_affine_map]
      simp only [Set.image_image, f.apply_symm_apply, Set.image_id']
    calc
      volume (simplexSet T) = ENNReal.ofReal |LinearMap.det f.linear.toLinearMap| * volume (simplexSet U) := by
        conv_lhs => rw [hTU]
        exact volume_affine_image f _
      _ ≤ ENNReal.ofReal |LinearMap.det f.linear.toLinearMap| * volume (simplexSet S) :=
        mul_le_mul_right (h.2 U hU) _
      _ = volume (simplexSet (affineSimplex f S)) := by
        rw [simplexSet_affine_map, volume_affine_image]

private theorem affine_homothety_apply {d : ℕ} (f : Space d ≃ᵃ[ℝ] Space d)
    (c x : Space d) (r : ℝ) :
    f (c + r • (x - c)) = f c + r • (f x - f c) := by
  have h := f.map_vadd c (r • (x - c))
  have hv := f.toAffineMap.linearMap_vsub x c
  simp only [vadd_eq_add, vsub_eq_sub, map_smul] at h hv
  rw [add_comm c, h]
  change r • f.linear (x - c) + f c = f c + r • (f x - f c)
  change f.linear (x - c) = f x - f c at hv
  rw [hv, add_comm]

/-- The original centroid, rather than a chosen center, commutes with affine normalization. -/
theorem centeredDilation_affine_map {d : ℕ} (S : Affine.Simplex ℝ (Space d) d)
    (f : Space d ≃ᵃ[ℝ] Space d) (t : ℝ) :
    centeredDilation (affineSimplex f S) t = f '' centeredDilation S t := by
  have hc : (affineSimplex f S).centroid = f S.centroid :=
    S.centroid_map f.toAffineMap (fun _ _ h => f.injective h)
  unfold centeredDilation
  rw [hc, simplexSet_affine_map, Set.image_image, Set.image_image]
  congr 1
  funext x
  exact (affine_homothety_apply f S.centroid x (1 + t)).symm

/-- The literal infimum-based excess in Targets is affine invariant, for the same simplex. -/
theorem excess_affine_image {d : ℕ} (S : Affine.Simplex ℝ (Space d) d)
    (f : Space d ≃ᵃ[ℝ] Space d) (A : Set (Space d)) :
    excess (f '' A) (affineSimplex f S) = excess A S := by
  unfold excess
  congr 1
  ext t
  change (0 ≤ t ∧ f '' A ⊆ centeredDilation (affineSimplex f S) t) ↔
    (0 ≤ t ∧ A ⊆ centeredDilation S t)
  rw [centeredDilation_affine_map]
  exact and_congr_right (fun _ => Set.image_subset_image_iff f.injective)

/-- Positivity of true barycentric coordinates puts the genuine centroid in the interior. -/
theorem simplex_centroid_interior {d : ℕ} (S : Affine.Simplex ℝ (Space d) d) :
    S.centroid ∈ interior (simplexSet S) := by
  change S.centroid ∈ interior (convexHull ℝ (Set.range (fullBasis S)))
  rw [(fullBasis S).interior_convexHull]
  intro i
  have hc := (fullBasis S).coord_apply_centroid (s := Finset.univ) (i := i) (Finset.mem_univ i)
  change (fullBasis S).coord i S.centroid = _ at hc
  rw [hc]
  simp only [Finset.card_univ, Fintype.card_fin]
  positivity

/-- An actual positive closed ball about the original centroid is derived, not assumed. -/
theorem simplex_centroid_ball {d : ℕ} (S : Affine.Simplex ℝ (Space d) d) :
    ∃ r : ℝ, 0 < r ∧ closedBall S.centroid r ⊆ simplexSet S := by
  exact Metric.nhds_basis_closedBall.mem_iff.mp
    (mem_interior_iff_mem_nhds.mp (simplex_centroid_interior S))

/-- Every genuine simplex admits an actual invertible centered unit-ball normalization.
This constructs a translation and positive scaling; no regularity or universal radius bound is asserted. -/
theorem exists_centered_unit_normalization {d : ℕ} (S : Affine.Simplex ℝ (Space d) d) :
    ∃ f : Space d ≃ᵃ[ℝ] Space d,
      (affineSimplex f S).centroid = 0 ∧
      closedBall (0 : Space d) 1 ⊆ simplexSet (affineSimplex f S) := by
  obtain ⟨r, hr, hball⟩ := simplex_centroid_ball S
  let f : Space d ≃ᵃ[ℝ] Space d := AffineEquiv.ofLinearEquiv
    (LinearEquiv.smulOfNeZero ℝ (Space d) r⁻¹ (inv_ne_zero hr.ne')) S.centroid 0
  have hf (x : Space d) : f x = r⁻¹ • (x - S.centroid) := by
    simp [f, vsub_eq_sub, vadd_eq_add]
  refine ⟨f, ?_, ?_⟩
  · rw [show (affineSimplex f S).centroid = f S.centroid from
      S.centroid_map f.toAffineMap (fun _ _ h => f.injective h), hf]
    simp
  · intro x hx
    rw [simplexSet_affine_map]
    refine ⟨S.centroid + r • x, hball ?_, ?_⟩
    · rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_eq_abs, abs_of_pos hr]
      have hxnorm : ‖x‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hx
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hxnorm hr.le
    · rw [hf, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]

/-- The normalized inclusion is pulled back to the literal original-centroid excess.
Only genuine projected volumes in the specified affine coordinates are analytic inputs. -/
theorem excess_of_projection_deficit_after_affine {d : ℕ} (hd : 2 ≤ d)
    (f : Space d ≃ᵃ[ℝ] Space d) (K : ConvexBody (Space d))
    (P S : Affine.Simplex ℝ (Space d) d) (M η : ℝ)
    (hmax : maximumInscribed K S) (hKP : (K : Set (Space d)) ⊆ simplexSet P)
    (hcentroid : (affineSimplex f S).centroid = 0)
    (hball : closedBall (0 : Space d) 1 ⊆ simplexSet (affineSimplex f S))
    (hbound : ∀ i, ‖(affineSimplex f P).points i‖ ≤ M)
    (hη : 0 ≤ η) (hgate : (d : ℝ) * projectionHausdorffBound d M η ≤ 1 / 8)
    (hdef : ∀ u : Space d, ‖u‖ = 1 →
      (projectedVolume (ℝ ∙ u)ᗮ (simplexBody (affineSimplex f P))).toReal -
        (projectedVolume (ℝ ∙ u)ᗮ (affineBody f K)).toReal ≤ η) :
    excess (K : Set (Space d)) S ≤ 2 * M * (d : ℝ) * projectionHausdorffBound d M η := by
  have hnormmax := (maximumInscribed_affine_iff f K S).mpr hmax
  have hnormKP : (affineBody f K : Set (Space d)) ⊆ simplexSet (affineSimplex f P) := by
    rw [simplexSet_affine_map]
    exact Set.image_mono hKP
  have hM : 0 ≤ M := (norm_nonneg _).trans (hbound 0)
  have hrho : 0 ≤ projectionHausdorffBound d M η := by
    unfold projectionHausdorffBound
    positivity
  have hcontain := retain_maximum_simplex_of_projection_deficit hd (affineBody f K)
    (affineSimplex f P) (affineSimplex f S) M η hnormmax hnormKP hbound hball hη hgate hdef
  have hnorm : excess (affineBody f K : Set (Space d)) (affineSimplex f S) ≤
      2 * M * (d : ℝ) * projectionHausdorffBound d M η := by
    unfold excess
    apply csInf_le
    · exact ⟨0, fun t ht => ht.1⟩
    · refine ⟨by positivity, ?_⟩
      simpa only [centeredDilation, hcentroid, sub_zero, zero_add, Set.image_smul] using hcontain
  exact excess_affine_image S f (K : Set (Space d)) ▸ hnorm

/-- Normalization and original-centroid restoration for every prescribed genuine maximum simplex.
The enclosing simplex and the actual projection-deficit estimate remain explicit inputs. -/
theorem maximum_simplex_normalized_geometric_endpoint {d : ℕ} (hd : 2 ≤ d)
    (K : ConvexBody (Space d)) (S : Affine.Simplex ℝ (Space d) d)
    (hmax : maximumInscribed K S) :
    ∃ f : Space d ≃ᵃ[ℝ] Space d,
      (affineSimplex f S).centroid = 0 ∧
      closedBall (0 : Space d) 1 ⊆ simplexSet (affineSimplex f S) ∧
      maximumInscribed (affineBody f K) (affineSimplex f S) ∧
      ∀ (P : Affine.Simplex ℝ (Space d) d) (M η : ℝ),
        (K : Set (Space d)) ⊆ simplexSet P →
        (∀ i, ‖(affineSimplex f P).points i‖ ≤ M) →
        0 ≤ η → (d : ℝ) * projectionHausdorffBound d M η ≤ 1 / 8 →
        (∀ u : Space d, ‖u‖ = 1 →
          (projectedVolume (ℝ ∙ u)ᗮ (simplexBody (affineSimplex f P))).toReal -
            (projectedVolume (ℝ ∙ u)ᗮ (affineBody f K)).toReal ≤ η) →
        excess (K : Set (Space d)) S ≤
          2 * M * (d : ℝ) * projectionHausdorffBound d M η := by
  obtain ⟨f, hc, hb⟩ := exists_centered_unit_normalization S
  refine ⟨f, hc, hb, (maximumInscribed_affine_iff f K S).mpr hmax, ?_⟩
  intro P M η hKP hbound hη hgate hdef
  exact excess_of_projection_deficit_after_affine hd f K P S M η hmax hKP hc hb
    hbound hη hgate hdef

end Entry005
