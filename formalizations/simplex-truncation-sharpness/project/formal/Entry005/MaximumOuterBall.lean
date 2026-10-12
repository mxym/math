import Entry005.AffineNormalization

noncomputable section
open Metric MeasureTheory MeasureTheory.Measure
open scoped BigOperators
namespace Entry005

/-- The genuine full affine basis underlying a full-dimensional simplex. -/
def simplexAffineBasis {d : ℕ} (S : Affine.Simplex ℝ (Space d) d) :
    AffineBasis (Fin (d + 1)) ℝ (Space d) :=
  ⟨S.points, S.independent, S.affineSpan_eq_top (by simp [Space])⟩

/-- The actual affine barycentric coordinate, not a stipulated coefficient. -/
def simplexCoord {d : ℕ} (S : Affine.Simplex ℝ (Space d) d)
    (i : Fin (d + 1)) : Space d →ᵃ[ℝ] ℝ := (simplexAffineBasis S).coord i

private def replacementMap {d : ℕ} (S : Affine.Simplex ℝ (Space d) d)
    (i : Fin (d + 1)) (x : Space d) : Space d →ᵃ[ℝ] Space d where
  toFun y := y + simplexCoord S i y • (x - S.points i)
  linear := LinearMap.id + (simplexCoord S i).linear.smulRight (x - S.points i)
  map_vadd' y v := by
    have hc := (simplexCoord S i).map_vadd y v
    simp only [vadd_eq_add] at hc ⊢
    simp only [hc, add_smul, LinearMap.add_apply, LinearMap.id_apply,
      LinearMap.smulRight_apply]
    abel

private theorem replacement_coord {d : ℕ} (S : Affine.Simplex ℝ (Space d) d)
    (i : Fin (d + 1)) (x y : Space d) :
    simplexCoord S i (replacementMap S i x y) =
      simplexCoord S i y * simplexCoord S i x := by
  have hv := (simplexCoord S i).linearMap_vsub x (S.points i)
  simp only [vsub_eq_sub] at hv
  have hi : simplexCoord S i (S.points i) = 1 := (simplexAffineBasis S).coord_apply_eq i
  have ha := (simplexCoord S i).map_vadd y (simplexCoord S i y • (x - S.points i))
  simp only [vadd_eq_add, map_smul, smul_eq_mul] at ha
  change simplexCoord S i (y + simplexCoord S i y • (x - S.points i)) = _
  rw [add_comm, ha, hv, hi]
  ring

private theorem replacement_bijective {d : ℕ} (S : Affine.Simplex ℝ (Space d) d)
    (i : Fin (d + 1)) (x : Space d) (hx : simplexCoord S i x ≠ 0) :
    Function.Bijective (replacementMap S i x) := by
  constructor
  · intro y z h
    have hc := congrArg (simplexCoord S i) h
    rw [replacement_coord, replacement_coord] at hc
    have hyz : simplexCoord S i y = simplexCoord S i z := mul_right_cancel₀ hx hc
    change y + simplexCoord S i y • (x - S.points i) =
      z + simplexCoord S i z • (x - S.points i) at h
    rw [hyz] at h
    exact add_right_cancel h
  · intro y
    refine ⟨y - (simplexCoord S i y / simplexCoord S i x) • (x - S.points i), ?_⟩
    have hv := (simplexCoord S i).linearMap_vsub x (S.points i)
    simp only [vsub_eq_sub] at hv
    have hi : simplexCoord S i (S.points i) = 1 := (simplexAffineBasis S).coord_apply_eq i
    have ha := (simplexCoord S i).map_vadd y
      (-(simplexCoord S i y / simplexCoord S i x) • (x - S.points i))
    simp only [vadd_eq_add, map_smul, smul_eq_mul, hv, hi] at ha
    have hc : simplexCoord S i
        (y - (simplexCoord S i y / simplexCoord S i x) • (x - S.points i)) =
        simplexCoord S i y / simplexCoord S i x := by
      rw [sub_eq_add_neg, ← neg_smul, add_comm, ha]
      field_simp
      ring
    change y - (simplexCoord S i y / simplexCoord S i x) • (x - S.points i) +
      simplexCoord S i (y - (simplexCoord S i y / simplexCoord S i x) •
        (x - S.points i)) • (x - S.points i) = y
    rw [hc, sub_add_cancel]

private def replacementEquiv {d : ℕ} (S : Affine.Simplex ℝ (Space d) d)
    (i : Fin (d + 1)) (x : Space d) (hx : simplexCoord S i x ≠ 0) :
    Space d ≃ᵃ[ℝ] Space d := AffineEquiv.ofBijective (replacement_bijective S i x hx)

private theorem replacement_points {d : ℕ} (S : Affine.Simplex ℝ (Space d) d)
    (i : Fin (d + 1)) (x : Space d) (j : Fin (d + 1)) :
    replacementMap S i x (S.points j) = if j = i then x else S.points j := by
  classical
  have hc : simplexCoord S i (S.points j) = if j = i then 1 else 0 := by
    change (simplexAffineBasis S).coord i ((simplexAffineBasis S) j) = _
    rw [AffineBasis.coord_apply]
    simp only [eq_comm]
  change S.points j + simplexCoord S i (S.points j) • (x - S.points i) = _
  rw [hc]
  split_ifs with h
  · subst j
    simp
  · simp

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

private theorem replacement_augmented {d : ℕ} (S : Affine.Simplex ℝ (Space d) d)
    (i : Fin (d + 1)) (x : Space d) :
    augmentedVertices (fun j => replacementMap S i x (S.points j)) =
      (augmentedVertices S.points).updateCol i
        (fun k => ∑ j, simplexCoord S j x • augmentedVertices S.points k j) := by
  classical
  have hcol (k : Fin (d + 1)) :
      (∑ j, simplexCoord S j x • augmentedVertices S.points k j) =
        Fin.cases 1 (fun l => x l) k := by
    refine Fin.cases ?_ (fun l => ?_) k
    · simp only [augmentedVertices, Fin.cases_zero, smul_eq_mul, mul_one]
      exact (simplexAffineBasis S).sum_coord_apply_eq_one x
    · simp only [augmentedVertices, Fin.cases_succ, smul_eq_mul]
      have h := congrArg (fun y : Space d => y l)
        ((simplexAffineBasis S).linear_combination_coord_eq_self x)
      change (∑ j, simplexCoord S j x • S.points j) l = x l at h
      simpa only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul] using h
  ext k j
  rw [Matrix.updateCol_apply, hcol]
  simp only [augmentedVertices]
  simp_rw [replacement_points]
  by_cases hj : j = i
  · simp [hj]
  · simp [hj]

private theorem replacement_det {d : ℕ} (hd : 1 ≤ d)
    (S : Affine.Simplex ℝ (Space d) d) (i : Fin (d + 1)) (x : Space d) :
    LinearMap.det (replacementMap S i x).linear = simplexCoord S i x := by
  have hm := congrArg Matrix.det (homogeneous_mul (replacementMap S i x) S.points)
  rw [Matrix.det_mul, homogeneous_det, replacement_augmented,
    Matrix.det_updateCol_sum, smul_eq_mul] at hm
  exact mul_right_cancel₀ (simplexMatrixVolumeInterface d hd S S (fun _ h => h)).1 hm

/-- Nonzero true coordinate gives a genuine invertible vertex replacement, with
its actual Haar volume computed rather than assumed. -/
theorem vertex_replacement_volume {d : ℕ} (hd : 1 ≤ d)
    (S : Affine.Simplex ℝ (Space d) d) (i : Fin (d + 1)) (x : Space d)
    (hx : simplexCoord S i x ≠ 0) :
    ∃ f : Space d ≃ᵃ[ℝ] Space d,
      (∀ j, f (S.points j) = if j = i then x else S.points j) ∧
      volume (simplexSet (affineSimplex f S)) =
        ENNReal.ofReal |simplexCoord S i x| * volume (simplexSet S) := by
  let f := replacementEquiv S i x hx
  refine ⟨f, replacement_points S i x, ?_⟩
  rw [simplexSet_affine_map, volume_affine_image]
  have hfdet : LinearMap.det f.linear.toLinearMap = simplexCoord S i x :=
    replacement_det hd S i x
  rw [hfdet]

/-- Maximality bounds every actual barycentric coordinate in absolute value.
The proof constructs the genuine simplex obtained by replacing vertex `i` by `x`
and computes its actual volume through its actual affine determinant. -/
theorem maximumInscribed_coord_abs_le_one {d : ℕ} (hd : 1 ≤ d)
    (K : ConvexBody (Space d)) (S : Affine.Simplex ℝ (Space d) d)
    (hmax : maximumInscribed K S) (x : Space d) (hx : x ∈ (K : Set (Space d)))
    (i : Fin (d + 1)) : |simplexCoord S i x| ≤ 1 := by
  classical
  by_cases hc : simplexCoord S i x = 0
  · simp [hc]
  obtain ⟨f, hfpoints, hfvolume⟩ := vertex_replacement_volume hd S i x hc
  let T := affineSimplex f S
  have hT : simplexSet T ⊆ (K : Set (Space d)) := by
    apply convexHull_min ?_ K.convex
    rintro _ ⟨j, rfl⟩
    change f (S.points j) ∈ (K : Set (Space d))
    rw [hfpoints]
    split_ifs
    · exact hx
    · exact hmax.1 (subset_convexHull ℝ (Set.range S.points) ⟨j, rfl⟩)
  have hv := hmax.2 T hT
  change volume (simplexSet (affineSimplex f S)) ≤ volume (simplexSet S) at hv
  rw [hfvolume] at hv
  have hvol := simplexMatrixVolumeInterface d hd S S (fun _ h => h)
  have hfinite : ENNReal.ofReal |simplexCoord S i x| * volume (simplexSet S) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hvol.2.1
  have hr := (ENNReal.toReal_le_toReal hfinite hvol.2.1).mpr hv
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)] at hr
  have hp := hvol.2.2.2.1
  nlinarith

/-- A prescribed genuine maximum simplex controls the entire body's outer radius.
No containing ball for the body is assumed. -/
theorem maximumInscribed_outer_ball {d : ℕ} (hd : 1 ≤ d)
    (K : ConvexBody (Space d)) (S : Affine.Simplex ℝ (Space d) d)
    (hmax : maximumInscribed K S) (R : ℝ) (hR : ∀ i, ‖S.points i‖ ≤ R) :
    (K : Set (Space d)) ⊆ closedBall 0 (((d : ℝ) + 1) * R) := by
  intro x hx
  have hcoords : ∑ i, simplexCoord S i x • S.points i = x :=
    (simplexAffineBasis S).linear_combination_coord_eq_self x
  have hnorm : ‖x‖ ≤ ((d : ℝ) + 1) * R := by
    calc
      ‖x‖ = ‖∑ i, simplexCoord S i x • S.points i‖ := congrArg norm hcoords.symm
      _ ≤ ∑ i, ‖simplexCoord S i x • S.points i‖ := norm_sum_le _ _
      _ = ∑ i, |simplexCoord S i x| * ‖S.points i‖ := by
        simp only [norm_smul, Real.norm_eq_abs]
      _ ≤ ∑ _i : Fin (d + 1), R := by
        apply Finset.sum_le_sum
        intro i _
        calc
          |simplexCoord S i x| * ‖S.points i‖ ≤ 1 * ‖S.points i‖ :=
            mul_le_mul_of_nonneg_right (maximumInscribed_coord_abs_le_one hd K S hmax x hx i)
              (norm_nonneg _)
          _ ≤ R := by simpa using hR i
      _ = ((d : ℝ) + 1) * R := by simp
  simpa only [mem_closedBall, dist_zero_right] using hnorm

/-- The literal published radius `R0 d = d (d + 1)` follows from norm-`d` vertices. -/
theorem maximumInscribed_R0_ball {d : ℕ} (hd : 1 ≤ d)
    (K : ConvexBody (Space d)) (S : Affine.Simplex ℝ (Space d) d)
    (hmax : maximumInscribed K S) (hR : ∀ i, ‖S.points i‖ ≤ (d : ℝ)) :
    (K : Set (Space d)) ⊆ closedBall 0 (R0 d) := by
  simpa only [R0, mul_comm] using maximumInscribed_outer_ball hd K S hmax (d : ℝ) hR

end Entry005
