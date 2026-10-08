import Entry005.FacetRadialMass
import Entry005.ConeLawFinite

noncomputable section
open Metric MeasureTheory Module
open scoped BigOperators RealInnerProductSpace

namespace Entry005

section ActualFiniteLaw

variable {ι : Type*} [Fintype ι] {d : ℕ}

/-- The cone law of the actual finite halfspace body. Its areas are actual
intrinsic facet volumes and its normalization is actual dimension-volume. -/
def finiteHalfspaceConeLaw (n : ι → Space d) (h : ι → ℝ) : Measure (Fin d → ℝ) :=
  finiteConeLaw (finiteHalfspaceFacetArea n h) h (fun i j => n i j)
    ((finrank ℝ (Space d) : ℝ) * (volume (finiteHalfspaceSet n h)).toReal)

omit [Fintype ι] in
theorem finite_halfspace_unit_ball_heights (n : ι → Space d) (h : ι → ℝ)
    (hn : ∀ i, ‖n i‖ = 1) (hb : closedBall (0 : Space d) 1 ⊆ finiteHalfspaceSet n h) :
    ∀ i, 1 ≤ h i := by
  intro i
  have hni : n i ∈ closedBall (0 : Space d) 1 := by
    simpa only [mem_closedBall, dist_zero_right, hn i] using (le_refl (1 : ℝ))
  have hh := hb hni i
  simpa only [real_inner_self_eq_norm_sq, hn i, one_pow] using hh

theorem space_inner_eq_raw_dot (u v : Space d) :
    inner ℝ u v = dotProduct (fun j => u j) (fun j => v j) := by
  simp [PiLp.inner_apply, dotProduct, mul_comm]

variable [Nontrivial (Space d)]

omit [Nontrivial (Space d)] in
theorem finite_halfspace_normal_balance_coordinates (n : ι → Space d) (h : ι → ℝ)
    (hn : ∀ i, ‖n i‖ = 1) (hinj : Function.Injective n)
    (hc : IsCompact (finiteHalfspaceSet n h)) :
    ∀ j, ∑ i, finiteHalfspaceFacetArea n h i * n i j = 0 := by
  intro j
  have hbal := finite_halfspace_normal_balance n h hn hinj hc
  simpa using congrArg (fun z : Space d => z j) hbal

/-- Probability follows from the proved actual radial-facet mass identity. -/
theorem finite_halfspace_cone_probability (n : ι → Space d) (h : ι → ℝ)
    (hn : ∀ i, ‖n i‖ = 1) (hh : ∀ i, 0 < h i) (hinj : Function.Injective n)
    (hc : IsCompact (finiteHalfspaceSet n h)) : IsProbabilityMeasure (finiteHalfspaceConeLaw n h) := by
  apply finite_cone_probability
  · exact finite_halfspace_facet_area_nonneg n h
  · exact hh
  · exact finite_halfspace_normalization_pos n h hn hh hc
  · exact finite_halfspace_facet_mass n h hn hh hinj hc

theorem finite_halfspace_cone_centered (n : ι → Space d) (h : ι → ℝ)
    (hn : ∀ i, ‖n i‖ = 1) (hh : ∀ i, 0 < h i) (hinj : Function.Injective n)
    (hc : IsCompact (finiteHalfspaceSet n h)) :
    ∀ j, (∫ x, x j ∂finiteHalfspaceConeLaw n h) = 0 := by
  apply finite_cone_centered
  · exact finite_halfspace_facet_area_nonneg n h
  · exact hh
  · exact finite_halfspace_normalization_pos n h hn hh hc
  · exact finite_halfspace_normal_balance_coordinates n h hn hinj hc

omit [Nontrivial (Space d)] in
theorem finite_halfspace_cone_ae_unit_ball (n : ι → Space d) (h : ι → ℝ)
    (hn : ∀ i, ‖n i‖ = 1) (hb : closedBall (0 : Space d) 1 ⊆ finiteHalfspaceSet n h) :
    ∀ᵐ x ∂finiteHalfspaceConeLaw n h, ‖WithLp.toLp 2 x‖ ≤ 1 := by
  have hh := finite_halfspace_unit_ball_heights n h hn hb
  apply finite_cone_ae_unit_ball
  · intro i; linarith [hh i]
  · intro i
    have heq : WithLp.toLp 2 (fun j => n i j) = n i := by ext j; rfl
    rw [heq, hn i]
    exact hh i

omit [Nontrivial (Space d)] in
theorem finite_halfspace_cone_support_unit_ball (n : ι → Space d) (h : ι → ℝ)
    (hn : ∀ i, ‖n i‖ = 1) (hb : closedBall (0 : Space d) 1 ⊆ finiteHalfspaceSet n h) :
    ∀ x ∈ (finiteHalfspaceConeLaw n h).support, ‖WithLp.toLp 2 x‖ ≤ 1 :=
  unit_ball_support_bound _ (finite_halfspace_cone_ae_unit_ball n h hn hb)

omit [Nontrivial (Space d)] in
theorem finite_halfspace_brightness_normal_sum (n : ι → Space d) (h : ι → ℝ)
    (hn : ∀ i, ‖n i‖ = 1) (hinj : Function.Injective n)
    (hc : IsCompact (finiteHalfspaceSet n h)) (u : Space d) (hu : ‖u‖ = 1) :
    (∑ i, finiteHalfspaceFacetArea n h i * |dotProduct (fun j => u j) (fun j => n i j)|) =
      2 * projectionVolumeSet (finiteHalfspaceSet n h) u := by
  have hcf := finite_halfspace_cauchy n h hn hinj hc u hu
  have heq : (∑ i, finiteHalfspaceFacetArea n h i * |dotProduct (fun j => u j) (fun j => n i j)|) =
      ∑ i, |inner ℝ (n i) u| * finiteHalfspaceFacetArea n h i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← space_inner_eq_raw_dot, real_inner_comm u (n i)]
    ring
  rw [heq]
  linarith

/-- The actual law's directional absolute moment equals actual brightness
times two divided by its proved dimension-volume normalization. -/
theorem finite_halfspace_cone_absolute_brightness (n : ι → Space d) (h : ι → ℝ)
    (hn : ∀ i, ‖n i‖ = 1) (hh : ∀ i, 0 < h i) (hinj : Function.Injective n)
    (hc : IsCompact (finiteHalfspaceSet n h)) (u : Space d) (hu : ‖u‖ = 1) :
    (∫ x, |dotProduct (fun j => u j) x| ∂finiteHalfspaceConeLaw n h) =
      (2 * projectionVolumeSet (finiteHalfspaceSet n h) u) /
        ((finrank ℝ (Space d) : ℝ) * (volume (finiteHalfspaceSet n h)).toReal) := by
  rw [finiteHalfspaceConeLaw, finite_cone_absolute_direction _ _ _ _
    (finite_halfspace_facet_area_nonneg n h) hh (finite_halfspace_normalization_pos n h hn hh hc),
    finite_halfspace_brightness_normal_sum n h hn hinj hc u hu]

/-- Centering and actual Cauchy give the negative directional moment as
actual brightness divided by actual dimension-volume. -/
theorem finite_halfspace_cone_negative_brightness (n : ι → Space d) (h : ι → ℝ)
    (hn : ∀ i, ‖n i‖ = 1) (hh : ∀ i, 0 < h i) (hinj : Function.Injective n)
    (hc : IsCompact (finiteHalfspaceSet n h)) (u : Space d) (hu : ‖u‖ = 1) :
    negativeIntegral (finiteHalfspaceConeLaw n h) (fun x => dotProduct (fun j => u j) x) =
      projectionVolumeSet (finiteHalfspaceSet n h) u /
        ((finrank ℝ (Space d) : ℝ) * (volume (finiteHalfspaceSet n h)).toReal) := by
  rw [finiteHalfspaceConeLaw, finite_cone_negative_direction _ _ _ _
    (finite_halfspace_facet_area_nonneg n h) hh (finite_halfspace_normalization_pos n h hn hh hc)
    (finite_halfspace_normal_balance_coordinates n h hn hinj hc),
    finite_halfspace_brightness_normal_sum n h hn hinj hc u hu]
  ring

theorem unit_hyperplane_ball_volume (u : Space d) (hu : ‖u‖ = 1) :
    volume (closedBall (0 : (ℝ ∙ u)ᗮ) 1) = volume (closedBall (0 : Space (d - 1)) 1) := by
  have hd : 0 < d := by simpa [Space] using (finrank_pos : 0 < finrank ℝ (Space d))
  have hfact : Fact (finrank ℝ (Space d) = (d - 1) + 1) := ⟨by simp [Space]; omega⟩
  have hu0 : u ≠ 0 := by intro hz; simp [hz] at hu
  let b : OrthonormalBasis (Fin (d - 1)) ℝ (ℝ ∙ u)ᗮ :=
    OrthonormalBasis.fromOrthogonalSpanSingleton (d - 1) hu0
  have himage : b.repr '' closedBall (0 : (ℝ ∙ u)ᗮ) 1 = closedBall (0 : Space (d - 1)) 1 := by
    simpa only [map_zero] using b.repr.image_closedBall 0 1
  rw [← himage, isometry_volume_image]

omit [Fintype ι] in
theorem finite_halfspace_brightness_lower_of_unit_ball (n : ι → Space d) (h : ι → ℝ)
    (hc : IsCompact (finiteHalfspaceSet n h))
    (hb : closedBall (0 : Space d) 1 ⊆ finiteHalfspaceSet n h)
    (u : Space d) (hu : ‖u‖ = 1) :
    (volume (closedBall (0 : Space (d - 1)) 1)).toReal ≤
      projectionVolumeSet (finiteHalfspaceSet n h) u := by
  rw [← unit_hyperplane_ball_volume u hu]
  apply ENNReal.toReal_mono
  · exact (hc.image (ℝ ∙ u)ᗮ.orthogonalProjectionOnto.continuous).measure_ne_top
  · apply measure_mono
    intro z hz
    refine ⟨(z : Space d), hb ?_, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self z⟩
    simpa only [mem_closedBall, dist_zero_right, Submodule.norm_coe] using hz

/-- A concrete positive roundness coefficient for the actual cone law when
the actual body contains the Euclidean unit ball. -/
theorem finite_halfspace_cone_round_lower (n : ι → Space d) (h : ι → ℝ)
    (hn : ∀ i, ‖n i‖ = 1) (hh : ∀ i, 0 < h i) (hinj : Function.Injective n)
    (hc : IsCompact (finiteHalfspaceSet n h))
    (hb : closedBall (0 : Space d) 1 ⊆ finiteHalfspaceSet n h)
    (u : Space d) (hu : ‖u‖ = 1) :
    (volume (closedBall (0 : Space (d - 1)) 1)).toReal /
      ((finrank ℝ (Space d) : ℝ) * (volume (finiteHalfspaceSet n h)).toReal) ≤
      negativeIntegral (finiteHalfspaceConeLaw n h) (fun x => dotProduct (fun j => u j) x) := by
  rw [finite_halfspace_cone_negative_brightness n h hn hh hinj hc u hu]
  exact div_le_div_of_nonneg_right (finite_halfspace_brightness_lower_of_unit_ball n h hc hb u hu)
    (finite_halfspace_normalization_pos n h hn hh hc).le

theorem finite_halfspace_cone_round_coefficient_pos (n : ι → Space d) (h : ι → ℝ)
    (hn : ∀ i, ‖n i‖ = 1) (hh : ∀ i, 0 < h i)
    (hc : IsCompact (finiteHalfspaceSet n h)) :
    0 < (volume (closedBall (0 : Space (d - 1)) 1)).toReal /
      ((finrank ℝ (Space d) : ℝ) * (volume (finiteHalfspaceSet n h)).toReal) := by
  apply div_pos
  · have hp : 0 < volume (ball (0 : Space (d - 1)) 1) :=
      isOpen_ball.measure_pos volume ⟨0, by simp⟩
    have hpc : 0 < volume (closedBall (0 : Space (d - 1)) 1) :=
      hp.trans_le (measure_mono ball_subset_closedBall)
    exact ENNReal.toReal_pos hpc.ne'
      (isCompact_closedBall (0 : Space (d - 1)) (1 : ℝ)).measure_ne_top
  · exact finite_halfspace_normalization_pos n h hn hh hc

end ActualFiniteLaw
end Entry005
