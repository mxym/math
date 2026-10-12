import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Entry005.RadialPowerIntegral

/-! Literal radial slices give the generic cone-volume formula. The cone is
the actual scalar image of a compact base at positive height; no body-level
facet coverage or pyramid identity is assumed. -/

noncomputable section
open MeasureTheory
open scoped Pointwise

namespace Entry005

section Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def radialCone (F : Set E) (h : ℝ) : Set (E × ℝ) :=
  {p | ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ z ∈ F, p = (t • z, t * h)}

theorem radial_cone_compact {F : Set E} (hF : IsCompact F) (h : ℝ) :
    IsCompact (radialCone F h) := by
  have heq : radialCone F h =
      (fun q : E × ℝ => (q.2 • q.1, q.2 * h)) '' (F ×ˢ Set.Icc (0 : ℝ) 1) := by
    ext p
    constructor
    · rintro ⟨t, ht, z, hz, rfl⟩
      exact ⟨(z, t), ⟨hz, ht⟩, rfl⟩
    · rintro ⟨⟨z, t⟩, ⟨hz, ht⟩, rfl⟩
      exact ⟨t, ht, z, hz, rfl⟩
  rw [heq]
  exact (hF.prod isCompact_Icc).image
    ((continuous_snd.smul continuous_fst).prodMk (continuous_snd.mul_const h))

theorem radial_cone_horizontal_slice {F : Set E} {h s : ℝ} (hh : 0 < h)
    (hs : s ∈ Set.Icc (0 : ℝ) h) :
    (fun x : E => (x, s)) ⁻¹' radialCone F h = (s / h) • F := by
  ext x
  constructor
  · rintro ⟨t, ht, z, hz, heq⟩
    have hst : s = t * h := congrArg Prod.snd heq
    have hx : x = t • z := congrArg Prod.fst heq
    have ht' : s / h = t := by rw [hst]; exact mul_div_cancel_right₀ t hh.ne'
    rw [ht', hx]
    exact Set.smul_mem_smul_set hz
  · rintro ⟨z, hz, rfl⟩
    refine ⟨s / h, ⟨div_nonneg hs.1 hh.le, (div_le_one hh).mpr hs.2⟩, z, hz, ?_⟩
    simp only [div_mul_cancel₀ _ hh.ne']

theorem radial_cone_horizontal_slice_empty {F : Set E} {h s : ℝ} (hh : 0 < h)
    (hs : s ∉ Set.Icc (0 : ℝ) h) :
    (fun x : E => (x, s)) ⁻¹' radialCone F h = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  rcases hx with ⟨t, ht, z, hz, heq⟩
  have hst : s = t * h := congrArg Prod.snd heq
  apply hs
  rw [hst]
  exact ⟨mul_nonneg ht.1 hh.le, by nlinarith [ht.2]⟩

end Geometry

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem radial_cone_horizontal_slice_volume {F : Set E} {h : ℝ} (hh : 0 < h) (s : ℝ) :
    volume ((fun x : E => (x, s)) ⁻¹' radialCone F h) =
      (Set.Icc (0 : ℝ) h).indicator
        (fun s => ENNReal.ofReal ((s / h) ^ Module.finrank ℝ E) * volume F) s := by
  by_cases hs : s ∈ Set.Icc (0 : ℝ) h
  · rw [Set.indicator_of_mem hs, radial_cone_horizontal_slice hh hs]
    exact Measure.addHaar_smul_of_nonneg volume (div_nonneg hs.1 hh.le) F
  · rw [Set.indicator_of_notMem hs, radial_cone_horizontal_slice_empty hh hs, measure_empty]

theorem radial_cone_horizontal_slice_volume_toReal {F : Set E} {h : ℝ}
    (hh : 0 < h) (s : ℝ) :
    (volume ((fun x : E => (x, s)) ⁻¹' radialCone F h)).toReal =
      (Set.Icc (0 : ℝ) h).indicator
        (fun s => (s / h) ^ Module.finrank ℝ E * (volume F).toReal) s := by
  rw [radial_cone_horizontal_slice_volume hh]
  by_cases hs : s ∈ Set.Icc (0 : ℝ) h
  · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg (div_nonneg hs.1 hh.le) _)]
  · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs, ENNReal.toReal_zero]

/-- The generic radial cone-volume formula follows from the actual slices
and product Fubini. Compactness suffices, including for the empty base. -/
theorem radial_cone_product_volume {F : Set E} (hF : IsCompact F) {h : ℝ} (hh : 0 < h) :
    ((volume.prod volume) (radialCone F h)).toReal =
      h / (Module.finrank ℝ E + 1 : ℝ) * (volume F).toReal := by
  have hC : MeasurableSet (radialCone F h) := (radial_cone_compact hF h).measurableSet
  have hm : Measurable (fun s : ℝ => volume ((fun x : E => (x, s)) ⁻¹' radialCone F h)) :=
    measurable_measure_prodMk_right hC
  have hfinite : ∀ s : ℝ, volume ((fun x : E => (x, s)) ⁻¹' radialCone F h) < ⊤ := by
    intro s
    rw [radial_cone_horizontal_slice_volume hh]
    by_cases hs : s ∈ Set.Icc (0 : ℝ) h
    · rw [Set.indicator_of_mem hs]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hF.measure_lt_top
    · rw [Set.indicator_of_notMem hs]
      exact ENNReal.zero_lt_top
  rw [Measure.prod_apply_symm hC,
    ← integral_toReal hm.aemeasurable (Filter.Eventually.of_forall hfinite)]
  simp_rw [radial_cone_horizontal_slice_volume_toReal hh]
  rw [integral_indicator measurableSet_Icc, integral_mul_const, radial_power_integral _ h hh]

/-- The same generic formula holds in the literal product Hilbert space. -/
theorem radial_cone_lp_volume {F : Set E} (hF : IsCompact F) {h : ℝ} (hh : 0 < h) :
    (volume ((WithLp.toLp 2) '' radialCone F h)).toReal =
      h / (Module.finrank ℝ E + 1 : ℝ) * (volume F).toReal := by
  have hm : MeasurableSet ((WithLp.toLp 2) '' radialCone F h) :=
    ((radial_cone_compact hF h).image (WithLp.prod_continuous_toLp 2 E ℝ)).measurableSet
  have hv := (WithLp.volume_preserving_toLp E ℝ).measure_preimage hm.nullMeasurableSet
  rw [Set.preimage_image_eq _ (WithLp.toLp_injective 2)] at hv
  rw [← hv]
  exact radial_cone_product_volume hF hh

end Volume

end Entry005
