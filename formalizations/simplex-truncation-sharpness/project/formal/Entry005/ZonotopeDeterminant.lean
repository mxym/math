import Entry005.ZonotopeVolume
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.LinearAlgebra.Multilinear.Curry

noncomputable section
open MeasureTheory Module
open scoped BigOperators RealInnerProductSpace

namespace Entry005

section Bases

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- Isometric transport preserves the volume of the actual finite segment sum. -/
theorem finite_zonotope_volume_isometry {ι : Type*} [Fintype ι] (g : ι → E)
    (f : E ≃ₗᵢ[ℝ] F) : volume (finiteZonotope g) =
      volume (finiteZonotope (fun i => f (g i))) := by
  have hs : MeasurableSet (f '' finiteZonotope g) :=
    ((finite_zonotope_compact g).image f.continuous).measurableSet
  have h := f.measurePreserving.measure_preimage hs.nullMeasurableSet
  rw [Set.preimage_image_eq _ f.injective] at h
  have heq : f '' finiteZonotope g = finiteZonotope (fun i => f (g i)) :=
    finite_zonotope_linear_image g f.toLinearMap
  rwa [heq] at h

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem finite_zonotope_subset_generator_span {ι : Type*} [Fintype ι] (g : ι → E) :
    finiteZonotope g ⊆ Submodule.span ℝ (Set.range g) := by
  rintro x ⟨t, ht, rfl⟩
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- A zonotope with fewer generators than ambient dimension has actual
ambient volume zero, rather than a formally defined determinant deficit. -/
theorem finite_zonotope_volume_zero_of_card_lt {ι : Type*} [Fintype ι] (g : ι → E)
    (hcard : Fintype.card ι < finrank ℝ E) : volume (finiteZonotope g) = 0 := by
  have hspan : Submodule.span ℝ (Set.range g) ≠ ⊤ := by
    intro hs
    exact (not_le_of_gt hcard) (finrank_le_of_span_eq_top hs)
  exact measure_mono_null (finite_zonotope_subset_generator_span g)
    (Measure.addHaar_submodule volume _ hspan)

variable {d : ℕ} [Fact (finrank ℝ E = d + 1)]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The orthogonal fiber space has the precise lower dimension. -/
theorem zonotope_orthogonal_finrank {v : E} (hv : v ≠ 0) :
    finrank ℝ (ℝ ∙ v)ᗮ = d := Submodule.finrank_orthogonal_span_singleton hv

/-- The projected zonotope's intrinsic volume is exactly that of its literal
coordinates in `EuclideanSpace ℝ (Fin d)`, through an orthonormal basis. -/
theorem finite_zonotope_projection_volume_coordinates {ι : Type*} [Fintype ι]
    (g : ι → E) {v : E} (hv : v ≠ 0) :
    volume (finiteZonotope (fun i => (ℝ ∙ v)ᗮ.orthogonalProjectionOnto (g i))) =
      volume (finiteZonotope (fun i =>
        (OrthonormalBasis.fromOrthogonalSpanSingleton d hv).repr
          ((ℝ ∙ v)ᗮ.orthogonalProjectionOnto (g i)))) := by
  exact finite_zonotope_volume_isometry _
    (OrthonormalBasis.fromOrthogonalSpanSingleton d hv).repr

end Bases

section LowDimensions

/-- Empty-dimensional Euclidean volume is one, including with any generator
count. This is the actual canonical Dirac volume in dimension zero. -/
theorem finite_zonotope_euclidean_zero_volume {ι : Type*} [Fintype ι]
    (g : ι → EuclideanSpace ℝ (Fin 0)) : volume (finiteZonotope g) = 1 := by
  have hZ : finiteZonotope g = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨y, hy⟩ := finite_zonotope_nonempty g
    convert hy using 1
    exact Subsingleton.elim _ _
  rw [hZ, volume_euclideanSpace_eq_dirac]
  simp

def euclideanOneCoordinates : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ :=
  PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)

theorem euclidean_one_coordinates_apply (x : EuclideanSpace ℝ (Fin 1)) :
    euclideanOneCoordinates x = x 0 := rfl

/-- The exact determinant-sum formula in the literal `EuclideanSpace` type
used by the targets when `d = 1`. -/
theorem finite_zonotope_euclidean_one_volume {ι : Type*} [Fintype ι]
    (g : ι → EuclideanSpace ℝ (Fin 1)) :
    (volume (finiteZonotope g)).toReal = 2 * ∑ i, |g i 0| := by
  have hm : MeasurePreserving euclideanOneCoordinates volume volume :=
    (volume_preserving_funUnique (Fin 1) ℝ).comp (PiLp.volume_preserving_ofLp (Fin 1))
  have hs : MeasurableSet (euclideanOneCoordinates '' finiteZonotope g) :=
    ((finite_zonotope_compact g).image euclideanOneCoordinates.continuous).measurableSet
  have hvol := hm.measure_preimage hs.nullMeasurableSet
  rw [Set.preimage_image_eq _ euclideanOneCoordinates.injective] at hvol
  have heq : euclideanOneCoordinates '' finiteZonotope g =
      finiteZonotope (fun i => euclideanOneCoordinates (g i)) :=
    finite_zonotope_linear_image g euclideanOneCoordinates.toLinearMap
  rw [heq] at hvol
  rw [hvol, finite_zonotope_real_volume]
  simp only [euclidean_one_coordinates_apply]

end LowDimensions

section DeterminantHeight

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {d : ℕ} [Fact (finrank ℝ E = d + 1)]

omit [FiniteDimensional ℝ E] in
theorem zonotope_orthogonal_projection_formula (v x : E) :
    ((ℝ ∙ v)ᗮ.orthogonalProjectionOnto x : E) =
      x - (inner ℝ v x / ‖v‖ ^ 2) • v := by
  change (ℝ ∙ v)ᗮ.starProjection x = _
  rw [Submodule.starProjection_orthogonal_val, Submodule.starProjection_singleton]
  rfl

omit [FiniteDimensional ℝ E] [Fact (finrank ℝ E = d + 1)] in
/-- Proved column operations from the projection-Jacobian branch. -/
theorem zonotope_alternating_projection_congr (e : Basis (Fin (d + 1)) ℝ E)
    (f : E [⋀^Fin (d + 1)]→ₗ[ℝ] ℝ) (v : E) (w : Fin d → E) :
    f (Fin.cons v w) =
      f (Fin.cons v (fun i => ((ℝ ∙ v)ᗮ.orthogonalProjectionOnto (w i) : E))) := by
  let A := e.toMatrix (Fin.cons v w)
  let B := e.toMatrix
    (Fin.cons v (fun i => ((ℝ ∙ v)ᗮ.orthogonalProjectionOnto (w i) : E)))
  let c : Fin (d + 1) → ℝ := Fin.cases 0 (fun i => inner ℝ v (w i) / ‖v‖ ^ 2)
  have hdet : A.det = B.det := by
    rw [← Matrix.det_transpose A, ← Matrix.det_transpose B]
    apply Matrix.det_eq_of_forall_row_eq_smul_add_const c 0 rfl
    intro i j
    induction i using Fin.cases with
    | zero => simp [A, B, c, Matrix.transpose_apply, Basis.toMatrix_apply]
    | succ i =>
      have hv : w i = ((ℝ ∙ v)ᗮ.orthogonalProjectionOnto (w i) : E) +
          (inner ℝ v (w i) / ‖v‖ ^ 2) • v := by
        rw [zonotope_orthogonal_projection_formula]
        exact (sub_add_cancel _ _).symm
      have hr := congrArg (fun x => e.repr x j) hv
      simpa [A, B, c, Matrix.transpose_apply, Basis.toMatrix_apply] using hr
  rw [f.eq_smul_basis_det e]
  simp only [AlternatingMap.smul_apply, smul_eq_mul, Basis.det_apply]
  exact congrArg (fun a => f e * a) hdet

/-- Binding the first variable retains actual multilinearity and alternation. -/
def contractFirst (f : E [⋀^Fin (d + 1)]→ₗ[ℝ] ℝ) (v : E) :
    E [⋀^Fin d]→ₗ[ℝ] ℝ :=
  { f.toMultilinearMap.curryLeft v with
    map_eq_zero_of_eq' w i j h hij :=
      f.map_eq_zero_of_eq _ (by simpa using h) ((Fin.succ_injective _).ne hij) }

omit [FiniteDimensional ℝ E] [Fact (finrank ℝ E = d + 1)] in
@[simp] theorem contractFirst_apply (f : E [⋀^Fin (d + 1)]→ₗ[ℝ] ℝ)
    (v : E) (w : Fin d → E) : contractFirst f v w = f (Fin.cons v w) := rfl

omit [FiniteDimensional ℝ E] in
/-- The determinant-height identity on actual orthogonal vectors, derived
from the ambient volume form and the intrinsic orthonormal determinant. -/
theorem volumeForm_height_orthogonal (o : Orientation ℝ E (Fin (d + 1)))
    (v : E) (b : OrthonormalBasis (Fin d) ℝ (ℝ ∙ v)ᗮ)
    (w : Fin d → (ℝ ∙ v)ᗮ) :
    |o.volumeForm (Fin.cons v (fun i => (w i : E)))| =
      ‖v‖ * |b.toBasis.det w| := by
  let A := (contractFirst o.volumeForm v).compLinearMap (ℝ ∙ v)ᗮ.subtype
  have hA : A = A b • b.toBasis.det := A.eq_smul_basis_det b.toBasis
  let z : Fin (d + 1) → E := Fin.cons v (fun k => (b k : E))
  have ho : Pairwise (fun i j : Fin (d + 1) => inner ℝ (z i) (z j) = 0) := by
    intro i j hij
    revert hij
    refine Fin.cases ?_ (fun i' => ?_) i
    · refine Fin.cases ?_ (fun j' => ?_) j
      · intro hij
        exact (hij rfl).elim
      · intro _
        simpa [z] using
          (Submodule.mem_orthogonal_singleton_iff_inner_right.mp (b j').property)
    · refine Fin.cases ?_ (fun j' => ?_) j
      · intro _
        simpa [z] using
          (Submodule.mem_orthogonal_singleton_iff_inner_left.mp (b i').property)
      · intro hij
        have hne : i' ≠ j' := fun h => hij (congrArg Fin.succ h)
        simpa [z] using b.orthonormal.inner_eq_zero hne
  have hnorm : |A b| = ‖v‖ := by
    change |o.volumeForm (Fin.cons v (fun i => (b i : E)))| = ‖v‖
    rw [o.abs_volumeForm_apply_of_pairwise_orthogonal ho, Fin.prod_univ_succ]
    change ‖v‖ * ∏ i, ‖b i‖ = ‖v‖
    simp [b.orthonormal.norm_eq_one]
  have heq := congrArg (fun a => |a w|) hA
  change |o.volumeForm (Fin.cons v (fun i => (w i : E)))| = _ at heq
  simpa only [AlternatingMap.smul_apply, smul_eq_mul, abs_mul, hnorm] using heq

omit [FiniteDimensional ℝ E] in
/-- The full determinant-height identity on arbitrary ambient vectors. -/
theorem orthonormal_determinant_height (bE : OrthonormalBasis (Fin (d + 1)) ℝ E)
    (v : E) (bH : OrthonormalBasis (Fin d) ℝ (ℝ ∙ v)ᗮ) (w : Fin d → E) :
    |bE.toBasis.det (Fin.cons v w)| =
      ‖v‖ * |bH.toBasis.det (fun i => (ℝ ∙ v)ᗮ.orthogonalProjectionOnto (w i))| := by
  let o := bE.toBasis.orientation
  rw [← o.volumeForm_robust' bE (Fin.cons v w),
    zonotope_alternating_projection_congr bE.toBasis o.volumeForm v w]
  exact volumeForm_height_orthogonal o v bH _

/-- The intrinsic determinant is the literal coordinate-column matrix determinant. -/
theorem orthonormal_basis_det_coordinates {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ F)
    (w : Fin n → F) :
    b.toBasis.det w = Matrix.det (fun i j => b.repr (w j) i) := by
  rw [Basis.det_apply]
  congr 1

end DeterminantHeight
end Entry005
