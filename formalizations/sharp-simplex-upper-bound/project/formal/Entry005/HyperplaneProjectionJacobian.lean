import Entry005.ZonotopeDeterminant
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

noncomputable section
open MeasureTheory Module
open scoped BigOperators RealInnerProductSpace

namespace Entry005

section ProjectionAlternation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {d : ℕ}

omit [FiniteDimensional ℝ E] in
theorem orthogonal_hyperplane_projection_formula (v x : E) :
    ((ℝ ∙ v)ᗮ.orthogonalProjectionOnto x : E) =
      x - (inner ℝ v x / ‖v‖ ^ 2) • v := by
  change (ℝ ∙ v)ᗮ.starProjection x = _
  rw [Submodule.starProjection_orthogonal_val, Submodule.starProjection_singleton]
  rfl

omit [FiniteDimensional ℝ E] in
/-- Orthogonal projection of the remaining columns preserves a top alternating
form with its first column fixed at the normal. This is a proved column
operation, not an assumed determinant-height identity. -/
theorem alternating_cons_projection_congr (e : Basis (Fin (d + 1)) ℝ E)
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
        rw [orthogonal_hyperplane_projection_formula]
        exact (sub_add_cancel _ _).symm
      have hr := congrArg (fun x => e.repr x j) hv
      simpa [A, B, c, Matrix.transpose_apply, Basis.toMatrix_apply] using hr
  rw [f.eq_smul_basis_det e]
  simp only [AlternatingMap.smul_apply, smul_eq_mul, Basis.det_apply]
  exact congrArg (fun a => f e * a) hdet

end ProjectionAlternation

section IntrinsicDeterminant

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {d : ℕ} [Fact (finrank ℝ E = d + 1)]

/-- On a family tangent to the normal `n`, contracting by `u` multiplies the
top alternating form by the normal component of `u`. The vanishing tangential
term follows from its actual lower-dimensional subspace. -/
theorem normal_contraction_factor (f : E [⋀^Fin (d + 1)]→ₗ[ℝ] ℝ)
    (n u : E) (hn : ‖n‖ = 1) (w : Fin d → (ℝ ∙ n)ᗮ) :
    f (Fin.cons u (fun i => (w i : E))) =
      inner ℝ n u * f (Fin.cons n (fun i => (w i : E))) := by
  have hn0 : n ≠ 0 := by intro h; simp [h] at hn
  let p := (ℝ ∙ n)ᗮ.orthogonalProjectionOnto u
  let z : Fin (d + 1) → (ℝ ∙ n)ᗮ := Fin.cons p w
  have hzero : f (Fin.cons (p : E) (fun i => (w i : E))) = 0 := by
    apply f.map_linearDependent
    intro hlin
    have hz : LinearIndependent ℝ z := by
      apply LinearIndependent.of_comp (ℝ ∙ n)ᗮ.subtype
      convert hlin using 1
      ext i
      induction i using Fin.cases <;> rfl
    have hdim : finrank ℝ (ℝ ∙ n)ᗮ = d := Submodule.finrank_orthogonal_span_singleton hn0
    have hcard := hz.fintype_card_le_finrank
    rw [Fintype.card_fin, hdim] at hcard
    omega
  have hdecomp : u = (inner ℝ n u) • n + (p : E) := by
    change u = (inner ℝ n u) • n + ((ℝ ∙ n)ᗮ.orthogonalProjectionOnto u : E)
    rw [orthogonal_hyperplane_projection_formula, hn]
    norm_num
  calc
    _ = f (Fin.cons ((inner ℝ n u) • n + (p : E)) (fun i => (w i : E))) :=
      congrArg (fun x => f (Fin.cons x (fun i => (w i : E)))) hdecomp
    _ = _ := by
      change f.toMultilinearMap (Fin.cons ((inner ℝ n u) • n + (p : E))
        (fun i => (w i : E))) = _
      rw [f.toMultilinearMap.cons_add, f.toMultilinearMap.cons_smul]
      change inner ℝ n u * f (Fin.cons n (fun i => (w i : E))) +
        f (Fin.cons (p : E) (fun i => (w i : E))) = _
      rw [hzero, add_zero]

/-- The actual intrinsic determinant of orthogonal hyperplane projection,
expressed in arbitrary orthonormal bases, has absolute value `|u·n|`. -/
theorem hyperplane_projection_basis_determinant (n u : E) (hn : ‖n‖ = 1)
    (hu : ‖u‖ = 1) (bN : OrthonormalBasis (Fin d) ℝ (ℝ ∙ n)ᗮ)
    (bU : OrthonormalBasis (Fin d) ℝ (ℝ ∙ u)ᗮ) :
    |bU.toBasis.det (fun i => (ℝ ∙ u)ᗮ.orthogonalProjectionOnto (bN i : E))| =
      |inner ℝ u n| := by
  let e : Basis (Fin (d + 1)) ℝ E :=
    Module.finBasisOfFinrankEq ℝ E (Fact.out : finrank ℝ E = d + 1)
  let o := e.orientation
  have hheight := volumeForm_height_orthogonal o u bU
    (fun i => (ℝ ∙ u)ᗮ.orthogonalProjectionOnto (bN i : E))
  rw [hu, one_mul, ← alternating_cons_projection_congr e o.volumeForm] at hheight
  have hfactor := normal_contraction_factor o.volumeForm n u hn bN
  rw [hfactor, abs_mul] at hheight
  have hnormal : |o.volumeForm (Fin.cons n (fun i => (bN i : E)))| = 1 := by
    rw [volumeForm_height_orthogonal o n bN bN, hn]
    change 1 * |bN.toBasis.det bN.toBasis| = 1
    rw [bN.toBasis.det_self]
    norm_num
  rw [hnormal, mul_one] at hheight
  simpa only [real_inner_comm n u] using hheight.symm

end IntrinsicDeterminant

section IntrinsicVolume

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

theorem isometry_volume_image (e : E ≃ₗᵢ[ℝ] F) (S : Set E) :
    volume (e '' S) = volume S := by
  rw [← e.measurePreserving.map_eq]
  let em : E ≃ᵐ F := e.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  change (volume.map em) (em '' S) = volume S
  rw [em.map_apply, Set.preimage_image_eq S em.injective]

theorem translation_volume_image (a : E) (S : Set E) :
    volume ((fun x => a + x) '' S) = volume S := by
  have heq : (fun x => a + x) '' S = (fun x => -a + x) ⁻¹' S := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨-a + x, hx, by simp⟩
  rw [heq]
  exact measure_preimage_add volume (-a) S

/-- Canonical Euclidean volume scaling between distinct equal-dimensional
spaces, through arbitrary orthonormal bases. It includes singular maps and all
sets; no geometric body-volume identity is an input. -/
theorem orthonormal_linear_image_volume {d : ℕ} (bE : OrthonormalBasis (Fin d) ℝ E)
    (bF : OrthonormalBasis (Fin d) ℝ F) (f : E →ₗ[ℝ] F) (S : Set E) :
    volume (f '' S) =
      ENNReal.ofReal |bF.toBasis.det (fun i => f (bE i))| * volume S := by
  let e : F ≃ₗᵢ[ℝ] E := bF.repr.trans bE.repr.symm
  let g : E →ₗ[ℝ] E := e.toLinearMap.comp f
  have hdet : LinearMap.det g = bF.toBasis.det (fun i => f (bE i)) := by
    rw [← g.det_toMatrix bE.toBasis, Basis.det_apply]
    congr 1
    ext i j
    simp [g, e, LinearMap.toMatrix_apply, Basis.toMatrix_apply,
      bE.coe_toBasis_repr_apply, bF.coe_toBasis_repr_apply]
  have himage : g '' S = e '' (f '' S) := Set.image_comp e f S
  rw [← isometry_volume_image e (f '' S), ← himage,
    Measure.addHaar_image_linearMap volume g S, hdet]

end IntrinsicVolume

section HyperplaneVolume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def hyperplaneProjection (n u : E) : (ℝ ∙ n)ᗮ →ₗ[ℝ] (ℝ ∙ u)ᗮ :=
  (ℝ ∙ u)ᗮ.orthogonalProjectionOnto.toLinearMap.comp (ℝ ∙ n)ᗮ.subtype

/-- Exact intrinsic Euclidean volume scaling for the actual projection
between hyperplanes. The singular case is included by the Haar image theorem,
which proves proper linear ranges have zero volume. -/
theorem hyperplane_projection_volume (n u : E) (hn : ‖n‖ = 1) (hu : ‖u‖ = 1)
    (S : Set (ℝ ∙ n)ᗮ) :
    volume (hyperplaneProjection n u '' S) =
      ENNReal.ofReal |inner ℝ u n| * volume S := by
  have hn0 : n ≠ 0 := by intro h; simp [h] at hn
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  let d := finrank ℝ E - 1
  have hpos : 1 ≤ finrank ℝ E := by
    have hspan : finrank ℝ (ℝ ∙ n) = 1 := finrank_span_singleton hn0
    calc
      1 = finrank ℝ (ℝ ∙ n) := hspan.symm
      _ ≤ finrank ℝ E := Submodule.finrank_le _
  have : Fact (finrank ℝ E = d + 1) := ⟨by dsimp [d]; omega⟩
  let bN : OrthonormalBasis (Fin d) ℝ (ℝ ∙ n)ᗮ :=
    OrthonormalBasis.fromOrthogonalSpanSingleton d hn0
  let bU : OrthonormalBasis (Fin d) ℝ (ℝ ∙ u)ᗮ :=
    OrthonormalBasis.fromOrthogonalSpanSingleton d hu0
  rw [orthonormal_linear_image_volume bN bU (hyperplaneProjection n u) S]
  have hdet := hyperplane_projection_basis_determinant n u hn hu bN bU
  exact congrArg (fun a => ENNReal.ofReal a * volume S) hdet

/-- Translation of the source hyperplane to support height `h` makes no
change to the intrinsic projected volume. This is the actual facet projection
Jacobian required by the finite-halfspace Cauchy construction. -/
theorem affine_hyperplane_projection_volume (n u : E) (hn : ‖n‖ = 1)
    (hu : ‖u‖ = 1) (h : ℝ) (S : Set (ℝ ∙ n)ᗮ) :
    volume ((ℝ ∙ u)ᗮ.orthogonalProjectionOnto ''
      ((fun z : (ℝ ∙ n)ᗮ => h • n + (z : E)) '' S)) =
      ENNReal.ofReal |inner ℝ u n| * volume S := by
  have heq : (ℝ ∙ u)ᗮ.orthogonalProjectionOnto ''
      ((fun z : (ℝ ∙ n)ᗮ => h • n + (z : E)) '' S) =
      (fun y : (ℝ ∙ u)ᗮ => (ℝ ∙ u)ᗮ.orthogonalProjectionOnto (h • n) + y) ''
        (hyperplaneProjection n u '' S) := by
    rw [← Set.image_comp, ← Set.image_comp]
    congr 1
    funext z
    exact map_add ((ℝ ∙ u)ᗮ.orthogonalProjectionOnto) (h • n) (z : E)
  rw [heq, translation_volume_image, hyperplane_projection_volume n u hn hu S]

theorem affine_hyperplane_projection_volume_zero (n u : E) (hn : ‖n‖ = 1)
    (hu : ‖u‖ = 1) (h : ℝ) (S : Set (ℝ ∙ n)ᗮ) (horth : inner ℝ u n = 0) :
    volume ((ℝ ∙ u)ᗮ.orthogonalProjectionOnto ''
      ((fun z : (ℝ ∙ n)ᗮ => h • n + (z : E)) '' S)) = 0 := by
  rw [affine_hyperplane_projection_volume n u hn hu h S, horth]
  simp

end HyperplaneVolume
end Entry005
