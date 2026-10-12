import Entry005.Handoff
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Convex.Topology
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Convex.Measure
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped BigOperators
namespace Entry005
namespace SimplexVolume

private def basis {d : ℕ} (P : Affine.Simplex ℝ (Space d) d) :
    AffineBasis (Fin (d + 1)) ℝ (Space d) :=
  ⟨P.points, P.independent, P.affineSpan_eq_top (by simp [Space])⟩

private theorem simplex_compact {d : ℕ} (P : Affine.Simplex ℝ (Space d) d) :
    IsCompact (simplexSet P) :=
  (Set.finite_range P.points).isCompact_convexHull ℝ

private theorem simplex_interior_nonempty {d : ℕ} (P : Affine.Simplex ℝ (Space d) d) :
    (interior (simplexSet P)).Nonempty := by
  apply (convex_convexHull ℝ (Set.range P.points)).interior_nonempty_iff_affineSpan_eq_top.mpr
  rw [affineSpan_convexHull]
  exact P.affineSpan_eq_top (by simp [Space])

private theorem simplex_volume_finite {d : ℕ} (P : Affine.Simplex ℝ (Space d) d) :
    volume (simplexSet P) ≠ ⊤ := (simplex_compact P).measure_ne_top

private theorem simplex_volume_positive {d : ℕ} (P : Affine.Simplex ℝ (Space d) d) :
    0 < (volume (simplexSet P)).toReal :=
  ENNReal.toReal_pos (measure_pos_of_nonempty_interior volume (simplex_interior_nonempty P)).ne'
    (simplex_volume_finite P)

private def e {d : ℕ} (k : Fin d) : Space d := EuclideanSpace.basisFun (Fin d) ℝ k

private theorem expand {d : ℕ} (x : Space d) : (∑ k, x k • e k) = x := by
  simpa [e] using (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr x

private theorem scalar_expand {d : ℕ} (f : Space d →ᵃ[ℝ] ℝ) (x : Space d) :
    f 0 + (∑ k, f.linear (e k) * x k) = f x := by
  have hlin : f.linear x = ∑ k, x k * f.linear (e k) := by
    calc
      f.linear x = f.linear (∑ k, x k • e k) := congrArg f.linear (expand x).symm
      _ = ∑ k, x k * f.linear (e k) := by
        rw [_root_.map_sum]
        simp only [map_smul, smul_eq_mul]
  have hf : f x = f.linear x + f 0 := congrFun f.decomp x
  rw [hf, hlin]
  simp only [mul_comm]
  exact add_comm _ _

private def inverseCandidate {d : ℕ} (P : Affine.Simplex ℝ (Space d) d) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  fun i j => Fin.cases ((basis P).coord i 0) (fun k => ((basis P).coord i).linear (e k)) j

private theorem candidate_mul {d : ℕ} (P : Affine.Simplex ℝ (Space d) d) :
    inverseCandidate P * augmentedVertices P.points = 1 := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  simp only [inverseCandidate, augmentedVertices, Fin.cases_zero, Fin.cases_succ, mul_one]
  rw [scalar_expand]
  exact (basis P).coord_apply i j

/-- Genuine affine independence and full dimension imply nonsingularity. -/
private theorem augmented_det_ne_zero {d : ℕ} (P : Affine.Simplex ℝ (Space d) d) :
    (augmentedVertices P.points).det ≠ 0 :=
  Matrix.det_ne_zero_of_left_inverse (candidate_mul P)

private def barycentric {d : ℕ} (P S : Affine.Simplex ℝ (Space d) d) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ := fun i j => (basis P).coord i (S.points j)

private theorem augmented_mul_barycentric {d : ℕ} (P S : Affine.Simplex ℝ (Space d) d) :
    augmentedVertices P.points * barycentric P S = augmentedVertices S.points := by
  ext i j
  refine Fin.cases ?_ (fun k => ?_) i
  · simp only [Matrix.mul_apply, augmentedVertices, Fin.cases_zero, one_mul, barycentric]
    exact (basis P).sum_coord_apply_eq_one (S.points j)
  · simp only [Matrix.mul_apply, augmentedVertices, Fin.cases_succ, barycentric]
    have h := congrArg (fun x : Space d => x k)
      ((basis P).linear_combination_coord_eq_self (S.points j))
    change (∑ i, (basis P).coord i (S.points j) • P.points i) k = (S.points j) k at h
    simpa only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using h

/-- The prescribed inverse-product matrix is exactly the true affine coordinates. -/
private theorem barycentric_matrix_eq {d : ℕ} (P S : Affine.Simplex ℝ (Space d) d) (i j) :
    simplexBarycentricMatrix P S i j = (basis P).coord i (S.points j) := by
  have hm := congrArg (fun A => (augmentedVertices P.points)⁻¹ * A)
    (augmented_mul_barycentric P S)
  rw [Matrix.nonsing_inv_mul_cancel_left (augmentedVertices P.points) _ (isUnit_iff_ne_zero.mpr (augmented_det_ne_zero P))] at hm
  exact congrArg (fun A => A i j) hm.symm

private def vertexMap {d : ℕ} (P S : Affine.Simplex ℝ (Space d) d) :
    Space d →ᵃ[ℝ] Space d where
  toFun x := ∑ i, (basis P).coord i x • S.points i
  linear := ∑ i, ((basis P).coord i).linear.smulRight (S.points i)
  map_vadd' x v := by
    have hc (i) : (basis P).coord i (v + x) = ((basis P).coord i).linear v +
        (basis P).coord i x := ((basis P).coord i).map_vadd x v
    change (∑ i, (basis P).coord i (v + x) • S.points i) = _
    simp only [hc, add_smul, Finset.sum_add_distrib, LinearMap.sum_apply,
      LinearMap.smulRight_apply, vadd_eq_add]

private theorem vertexMap_points {d : ℕ} (P S : Affine.Simplex ℝ (Space d) d) (j) :
    vertexMap P S (P.points j) = S.points j := by
  change (∑ i, (basis P).coord i ((basis P) j) • S.points i) = S.points j
  simp only [AffineBasis.coord_apply, ite_smul, one_smul, zero_smul]
  simp

private theorem vertexMap_image {d : ℕ} (P S : Affine.Simplex ℝ (Space d) d) :
    vertexMap P S '' simplexSet P = simplexSet S := by
  have himage : vertexMap P S '' Set.range P.points = Set.range S.points := by
    ext x
    constructor
    · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, (vertexMap_points P S j).symm⟩
    · rintro ⟨j, rfl⟩
      exact ⟨P.points j, ⟨j, rfl⟩, vertexMap_points P S j⟩
  rw [simplexSet, AffineMap.image_convexHull, himage]
  rfl

private def projection {d : ℕ} (k : Fin d) : Space d →ₗ[ℝ] ℝ where
  toFun x := x k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def homogeneous {d : ℕ} (f : Space d →ᵃ[ℝ] Space d) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  fun i j => Fin.cases (if j = 0 then 1 else 0)
    (fun k => Fin.cases (f 0 k) (fun l => f.linear (e l) k) j) i

private theorem homogeneous_mul {d : ℕ} (f : Space d →ᵃ[ℝ] Space d)
    (p : Fin (d + 1) → Space d) :
    homogeneous f * augmentedVertices p = augmentedVertices (fun j => f (p j)) := by
  ext i j
  refine Fin.cases ?_ (fun k => ?_) i
  · simp [Matrix.mul_apply, homogeneous, augmentedVertices]
  · rw [Matrix.mul_apply, Fin.sum_univ_succ]
    simp only [homogeneous, augmentedVertices, Fin.cases_zero, Fin.cases_succ, mul_one]
    exact scalar_expand ((projection k).toAffineMap.comp f) (p j)

private theorem homogeneous_det {d : ℕ} (f : Space d →ᵃ[ℝ] Space d) :
    (homogeneous f).det = LinearMap.det f.linear := by
  rw [Matrix.det_succ_row_zero]
  rw [Finset.sum_eq_single 0]
  · simp only [Fin.val_zero, pow_zero, homogeneous, Fin.cases_zero, ite_true, one_mul,
      Fin.succAbove_zero]
    have hmatrix : (homogeneous f).submatrix Fin.succ Fin.succ =
        LinearMap.toMatrix (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
          (EuclideanSpace.basisFun (Fin d) ℝ).toBasis f.linear := by
      ext i j
      simp only [homogeneous, Matrix.submatrix_apply, Fin.cases_succ, LinearMap.toMatrix_apply,
        OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]
      rfl
    rw [hmatrix, LinearMap.det_toMatrix]
  · intro j _ hj
    simp [homogeneous, hj]
  · simp

private theorem linear_det_eq_barycentric_det {d : ℕ}
    (P S : Affine.Simplex ℝ (Space d) d) :
    LinearMap.det (vertexMap P S).linear = (simplexBarycentricMatrix P S).det := by
  have hmul : homogeneous (vertexMap P S) * augmentedVertices P.points =
      augmentedVertices S.points := by
    simpa only [vertexMap_points] using homogeneous_mul (vertexMap P S) P.points
  have hd := congrArg Matrix.det hmul
  rw [Matrix.det_mul, homogeneous_det] at hd
  rw [simplexBarycentricMatrix, Matrix.det_mul, Matrix.det_nonsing_inv]
  simp only [Ring.inverse_eq_inv]
  calc
    _ = (augmentedVertices S.points).det / (augmentedVertices P.points).det :=
      (eq_div_iff (augmented_det_ne_zero P)).mpr hd
    _ = _ := by rw [div_eq_mul_inv, mul_comm]

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

private theorem determinant_volume_ratio {d : ℕ} (P S : Affine.Simplex ℝ (Space d) d) :
    |(simplexBarycentricMatrix P S).det| =
      (volume (simplexSet S)).toReal / (volume (simplexSet P)).toReal := by
  have hv := affine_image_volume (vertexMap P S) (simplexSet P)
  rw [vertexMap_image, linear_det_eq_barycentric_det] at hv
  have hr := congrArg ENNReal.toReal hv
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)] at hr
  apply (eq_div_iff (ne_of_gt (simplex_volume_positive P))).mpr
  exact hr.symm

end SimplexVolume
/-- The exact handoff interface, derived from genuine simplices and actual volume. -/
theorem simplexMatrixVolumeInterface : simplexMatrixVolumeInterfaceGoal := by
  intro d _hd P S hsubset
  refine ⟨SimplexVolume.augmented_det_ne_zero P,
    SimplexVolume.simplex_volume_finite P, SimplexVolume.simplex_volume_finite S,
    SimplexVolume.simplex_volume_positive P, ?_, ?_, ?_,
    SimplexVolume.determinant_volume_ratio P S⟩
  · intro i j
    rw [SimplexVolume.barycentric_matrix_eq]
    have hx : S.points j ∈ simplexSet P := hsubset
      (subset_convexHull ℝ (Set.range S.points) ⟨j, rfl⟩)
    change S.points j ∈ convexHull ℝ (Set.range (SimplexVolume.basis P)) at hx
    rw [(SimplexVolume.basis P).convexHull_eq_nonneg_coord] at hx
    exact hx i
  · intro j
    simp_rw [SimplexVolume.barycentric_matrix_eq]
    exact (SimplexVolume.basis P).sum_coord_apply_eq_one (S.points j)
  · intro j
    simp_rw [SimplexVolume.barycentric_matrix_eq]
    exact (SimplexVolume.basis P).linear_combination_coord_eq_self (S.points j)

end Entry005
