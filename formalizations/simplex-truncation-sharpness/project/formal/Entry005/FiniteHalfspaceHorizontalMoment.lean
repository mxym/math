import Entry005.FiniteLawZonotopeMoment
import Entry005.ProjectionVolumeSqueeze

/-! The actual horizontal first determinant moment of a finite halfspace
cone law equals the actual projection-body volume with its geometric normalization. -/

noncomputable section
open MeasureTheory Module
open scoped BigOperators Pointwise

namespace Entry005

theorem finite_zonotope_scaled_generators {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (g : ι → E) (c : ℝ) :
    finiteZonotope (fun i => c • g i) = c • finiteZonotope g := by
  simpa only [LinearMap.smul_apply, LinearMap.id_apply, Set.image_smul] using
    (finite_zonotope_linear_image g (c • (LinearMap.id : E →ₗ[ℝ] E))).symm

theorem finite_cone_weighted_zonotope_eq_normalized_generators {ι : Type*} [Fintype ι]
    {d : ℕ} (a h : ι → ℝ) (n : ι → Space d) (M : ℝ)
    (hh : ∀ i, 0 < h i) (hM : M ≠ 0) :
    finiteLawZonotope (fun i => a i * h i / M)
      (finiteConePoint (fun i j => n i j) h) = finiteZonotope (fun i => (a i / M) • n i) := by
  unfold finiteLawZonotope
  congr 1
  funext i
  ext j
  change (a i * h i / M) * (n i j / h i) = (a i / M) * n i j
  field_simp [hM, (hh i).ne']

theorem finite_halfspace_cone_zonotope_eq_scaled_projection_body {ι : Type*} [Fintype ι]
    {d : ℕ} (n : ι → Space d) (h : ι → ℝ) (M : ℝ)
    (hn : ∀ i, ‖n i‖ = 1) (hh : ∀ i, 0 < h i) (hinj : Function.Injective n)
    (hc : IsCompact (finiteHalfspaceSet n h)) (hM : M ≠ 0) :
    finiteLawZonotope (fun i => finiteHalfspaceFacetArea n h i * h i / M)
      (finiteConePoint (fun i j => n i j) h) =
        (2 / M : ℝ) • projectionBodySet (finiteHalfspaceSet n h) := by
  rw [finite_cone_weighted_zonotope_eq_normalized_generators _ _ _ _ hh hM,
    finite_halfspace_projection_body_eq_zonotope n h hn hinj hc,
    ← finite_zonotope_scaled_generators]
  congr 1
  funext i
  rw [smul_smul]
  congr 1
  field_simp [hM]

/-- The iid FIRST absolute determinant moment is determined by the actual
projection-body volume. Mass and Cauchy identities are proved dependencies. -/
theorem finite_halfspace_horizontal_first_moment {ι : Type*} [Fintype ι]
    {d : ℕ} [Nontrivial (Space d)] (n : ι → Space d) (h : ι → ℝ)
    (hn : ∀ i, ‖n i‖ = 1) (hh : ∀ i, 0 < h i) (hinj : Function.Injective n)
    (hc : IsCompact (finiteHalfspaceSet n h)) :
    (∫ base, |horizontalDeterminant base| ∂iidLaw (finiteHalfspaceConeLaw n h) d) =
      (d.factorial : ℝ) /
        ((d : ℝ) * (volume (finiteHalfspaceSet n h)).toReal) ^ d *
          (volume (projectionBodySet (finiteHalfspaceSet n h))).toReal := by
  classical
  let : MeasurableSpace ι := ⊤
  let : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩
  have hd : finrank ℝ (Space d) = d := by simp [Space]
  let a : ι → ℝ := finiteHalfspaceFacetArea n h
  let M : ℝ := (d : ℝ) * (volume (finiteHalfspaceSet n h)).toReal
  have hM : 0 < M := by
    simpa only [M, hd] using finite_halfspace_normalization_pos n h hn hh hc
  have hmass : ∑ i, a i * h i = M := by
    simpa only [a, M, hd] using finite_halfspace_facet_mass n h hn hh hinj hc
  have hvol := finite_cone_zonotope_volume_first_moment a h (fun i j => n i j) M
    (finite_halfspace_facet_area_nonneg n h) hh hM hmass
  rw [finite_halfspace_cone_zonotope_eq_scaled_projection_body n h M hn hh hinj hc hM.ne',
    real_volume_nonnegative_smul _ _ (div_nonneg (by norm_num) hM.le), hd, div_pow] at hvol
  have hfact : (d.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
  have hMpow : M ^ d ≠ 0 := pow_ne_zero d hM.ne'
  have hmoment :
      (∫ base, |horizontalDeterminant base|
        ∂iidLaw (finiteConeLaw a h (fun i j => n i j) M) d) =
      (d.factorial : ℝ) / M ^ d *
        (volume (projectionBodySet (finiteHalfspaceSet n h))).toReal := by
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hMpow).2
    field_simp [hfact, hMpow] at hvol
    simpa only [mul_comm] using hvol.symm
  simpa only [finiteHalfspaceConeLaw, hd, a, M] using hmoment

end Entry005
