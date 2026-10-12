import Entry005.PyramidZonotopeAlgebra

noncomputable section
open MeasureTheory Module
open scoped BigOperators RealInnerProductSpace Pointwise
namespace Entry005
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem pyramid_horizontal_projection (x : E) (t : ℝ) :
    (ℝ ∙ (pyramidBaseNormal : WithLp 2 (E × ℝ)))ᗮ.orthogonalProjectionOnto
      (WithLp.toLp 2 (x, t)) = pyramidBaseIsometry x := by
  apply Subtype.ext
  rw [orthogonal_hyperplane_projection_formula, pyramidBaseNormal_unit, inner_pyramidBaseNormal]
  change WithLp.toLp 2 (x, t) - (-t / 1 ^ 2) • WithLp.toLp 2 (0, (-1 : ℝ)) =
    WithLp.toLp 2 (x, 0)
  rw [← WithLp.toLp_smul, ← WithLp.toLp_sub]
  simp

variable {ι : Type*} [Fintype ι] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [Nontrivial E]

omit [Nontrivial E] in
theorem pyramid_side_horizontal_image (n : ι → E) (h : ι → ℝ)
    (hn : ∀ i, ‖n i‖ = 1) (hinj : Function.Injective n)
    (hc : IsCompact (finiteHalfspaceSet n h)) :
    (ℝ ∙ (pyramidBaseNormal : WithLp 2 (E × ℝ)))ᗮ.orthogonalProjectionOnto ''
      pyramidSideZonotope n h =
        pyramidBaseIsometry '' ((1 / Module.finrank ℝ E : ℝ) •
          projectionBodySet (finiteHalfspaceSet n h)) := by
  unfold pyramidSideZonotope
  have hQ : (ℝ ∙ (pyramidBaseNormal : WithLp 2 (E × ℝ)))ᗮ.orthogonalProjectionOnto ''
      finiteZonotope (fun i => (finiteHalfspaceFacetArea n h i / (2 * Module.finrank ℝ E : ℝ)) •
        WithLp.toLp 2 (n i, h i)) =
      finiteZonotope (fun i => (ℝ ∙ (pyramidBaseNormal : WithLp 2 (E × ℝ)))ᗮ.orthogonalProjectionOnto
        ((finiteHalfspaceFacetArea n h i / (2 * Module.finrank ℝ E : ℝ)) • WithLp.toLp 2 (n i, h i))) :=
    finite_zonotope_linear_image _ _
  rw [hQ]
  rw [finite_halfspace_projection_body_eq_zonotope n h hn hinj hc,
    ← finite_zonotope_scalar_image]
  have hJ : pyramidBaseIsometry '' finiteZonotope
      (fun i => (1 / Module.finrank ℝ E : ℝ) • ((finiteHalfspaceFacetArea n h i / 2) • n i)) =
      finiteZonotope (fun i => pyramidBaseIsometry
        ((1 / Module.finrank ℝ E : ℝ) • ((finiteHalfspaceFacetArea n h i / 2) • n i))) :=
    finite_zonotope_linear_image _ _
  rw [hJ]
  congr 1
  funext i
  simp only [map_smul, pyramid_horizontal_projection, smul_smul]
  congr 1
  ring

omit [Nontrivial E] in
theorem pyramid_side_horizontal_volume (n : ι → E) (h : ι → ℝ)
    (hn : ∀ i, ‖n i‖ = 1) (hinj : Function.Injective n)
    (hc : IsCompact (finiteHalfspaceSet n h)) :
    (volume ((ℝ ∙ (pyramidBaseNormal : WithLp 2 (E × ℝ)))ᗮ.orthogonalProjectionOnto ''
      pyramidSideZonotope n h)).toReal =
        (1 / Module.finrank ℝ E : ℝ) ^ Module.finrank ℝ E *
          (volume (projectionBodySet (finiteHalfspaceSet n h))).toReal := by
  rw [pyramid_side_horizontal_image n h hn hinj hc,
    IntrinsicLinearImageReuse.isometry_volume_image,
    Measure.addHaar_smul_of_nonneg volume (by positivity), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)]

/-- Actual projection-body volume of the pyramid is the lifted side zonotope
volume plus the real extrusion contribution of its base facet. -/
theorem pyramid_projection_body_volume_decomposition (n : ι → E) (h : ι → ℝ)
    (hn : ∀ i, ‖n i‖ = 1) (hh : ∀ i, 0 < h i) (hinj : Function.Injective n)
    (hc : IsCompact (finiteHalfspaceSet n h)) :
    (volume (projectionBodySet (pyramidSet (finiteHalfspaceSet n h)))).toReal =
      (volume (pyramidSideZonotope n h)).toReal +
        (volume (finiteHalfspaceSet n h)).toReal *
          (1 / Module.finrank ℝ E : ℝ) ^ Module.finrank ℝ E *
            (volume (projectionBodySet (finiteHalfspaceSet n h))).toReal := by
  let V := (volume (finiteHalfspaceSet n h)).toReal
  let g := pyramidProjectionGenerator n h
  have hV : 0 < V := finite_halfspace_volume_pos n h hn hh hc
  have hv : ‖g none‖ = V / 2 := by
    change ‖(V / 2) • (pyramidBaseNormal : WithLp 2 (E × ℝ))‖ = _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), pyramidBaseNormal_unit, mul_one]
  have hs : ℝ ∙ g none = ℝ ∙ (pyramidBaseNormal : WithLp 2 (E × ℝ)) :=
    Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr (by positivity : V / 2 ≠ 0)) _
  have hcZ := finite_zonotope_compact (fun i => g (some i))
  have hcQ := hcZ.image (ℝ ∙ g none)ᗮ.orthogonalProjectionOnto.continuous
  have hpvol : volume ((ℝ ∙ g none)ᗮ.orthogonalProjectionOnto '' finiteZonotope (fun i => g (some i))) =
      volume ((ℝ ∙ (pyramidBaseNormal : WithLp 2 (E × ℝ)))ᗮ.orthogonalProjectionOnto ''
        finiteZonotope (fun i => g (some i))) :=
    congrArg (fun P : Submodule ℝ (WithLp 2 (E × ℝ)) =>
      volume (Pᗮ.orthogonalProjectionOnto '' finiteZonotope (fun i => g (some i)))) hs
  rw [pyramid_projection_body_eq_zonotope n h hn hh hinj hc,
    finite_zonotope_option_volume]
  change (volume (finiteZonotope (fun i => g (some i))) + ENNReal.ofReal (2 * ‖g none‖) *
      volume ((ℝ ∙ g none)ᗮ.orthogonalProjectionOnto '' finiteZonotope (fun i => g (some i)))).toReal = _
  rw [ENNReal.toReal_add hcZ.measure_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hcQ.measure_ne_top),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), hv, hpvol]
  change (volume (pyramidSideZonotope n h)).toReal +
      (2 * (V / 2)) * (volume ((ℝ ∙ (pyramidBaseNormal : WithLp 2 (E × ℝ)))ᗮ.orthogonalProjectionOnto ''
        pyramidSideZonotope n h)).toReal = _
  rw [pyramid_side_horizontal_volume n h hn hinj hc]
  dsimp [V]
  ring

end Entry005
