import Entry005.ConeLawFinite
import Entry005.Targets

/-!
The actual finite symmetric-segment sum and its exact supporting halfspaces.
No assertion about facet measures, projection volumes, or zonotope volumes is
made in this module: those geometric identities remain distinct obligations.
-/

noncomputable section
open Metric MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace Entry005

section Zonotope

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def finiteZonotope (g : ι → E) : Set E :=
  (fun t : ι → ℝ => ∑ i, t i • g i) '' {t | ∀ i, t i ∈ Set.Icc (-1 : ℝ) 1}

def finiteZonotopeLinear (g : ι → E) : (ι → ℝ) →ₗ[ℝ] E where
  toFun t := ∑ i, t i • g i
  map_add' t s := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c t := by simp [mul_smul, Finset.smul_sum]

theorem finite_zonotope_convex (g : ι → E) : Convex ℝ (finiteZonotope g) := by
  have hc : Convex ℝ {t : ι → ℝ | ∀ i, t i ∈ Set.Icc (-1 : ℝ) 1} := by
    simpa [Set.pi] using (convex_pi (fun _ _ => convex_Icc (-1 : ℝ) 1) :
      Convex ℝ (Set.univ.pi (fun _ : ι => Set.Icc (-1 : ℝ) 1)))
  exact hc.linear_image (finiteZonotopeLinear g)

theorem finite_zonotope_compact (g : ι → E) : IsCompact (finiteZonotope g) := by
  apply (isCompact_pi_infinite (fun _ : ι => isCompact_Icc)).image
  exact continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const

theorem finite_zonotope_nonempty (g : ι → E) : (finiteZonotope g).Nonempty := by
  refine ⟨0, ?_⟩
  refine ⟨fun _ => 0, fun _ => ⟨by norm_num, by norm_num⟩, ?_⟩
  simp

theorem finite_zonotope_support_bound (g : ι → E) (u x : E)
    (hx : x ∈ finiteZonotope g) : inner ℝ u x ≤ ∑ i, |inner ℝ u (g i)| := by
  obtain ⟨t, ht, rfl⟩ := hx
  rw [inner_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [inner_smul_right]
  have ht' : |t i| ≤ 1 := abs_le.mpr (ht i)
  calc
    t i * inner ℝ u (g i) ≤ |t i * inner ℝ u (g i)| := le_abs_self _
    _ = |t i| * |inner ℝ u (g i)| := abs_mul _ _
    _ ≤ 1 * |inner ℝ u (g i)| := mul_le_mul_of_nonneg_right ht' (abs_nonneg _)
    _ = |inner ℝ u (g i)| := one_mul _

theorem finite_zonotope_support_attained (g : ι → E) (u : E) :
    ∃ x ∈ finiteZonotope g, inner ℝ u x = ∑ i, |inner ℝ u (g i)| := by
  classical
  let t : ι → ℝ := fun i => if 0 ≤ inner ℝ u (g i) then 1 else -1
  refine ⟨∑ i, t i • g i, ⟨t, ?_, rfl⟩, ?_⟩
  · intro i
    dsimp [t]
    split <;> constructor <;> norm_num
  · rw [inner_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [inner_smul_right]
    dsimp [t]
    split_ifs with hi
    · simp [abs_of_nonneg hi]
    · simp [abs_of_neg (lt_of_not_ge hi)]

/-- Exact actual-set equality. The converse uses the already proved nearest
point separating unit normal, so the halfspace representation is a conclusion.
-/
theorem finite_zonotope_eq_support_halfspaces (g : ι → E) :
    finiteZonotope g = {x | ∀ u : E, ‖u‖ = 1 →
      inner ℝ u x ≤ ∑ i, |inner ℝ u (g i)|} := by
  ext x
  constructor
  · intro hx u _
    exact finite_zonotope_support_bound g u x hx
  · intro hx
    by_contra hnot
    obtain ⟨k, hk, u, hs, hu, hgap, hsep, _⟩ :=
      closest_support (finiteZonotope g) (finite_zonotope_convex g)
        (finite_zonotope_compact g).isComplete (finite_zonotope_nonempty g) x hnot
    obtain ⟨y, hy, heq⟩ := finite_zonotope_support_attained g u
    have hky : (∑ i, |inner ℝ u (g i)|) ≤ inner ℝ u k := by
      rw [← heq]
      exact hsep y hy
    have hxu := hx u hu
    linarith

end Zonotope

section ActualProjectionReduction

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A reduction to a *separately unproved* projection-volume identity. The
conclusion identifies the literal `Targets` halfspace set with the actual
finite segment sum; this theorem neither supplies nor postulates the missing
Cauchy identity for any convex body.
-/
theorem projection_body_eq_finite_zonotope_of_projection_volume
    (K : Set E) (g : ι → E)
    (hbrightness : ∀ u : E, ‖u‖ = 1 →
      projectionVolumeSet K u = ∑ i, |inner ℝ u (g i)|) :
    projectionBodySet K = finiteZonotope g := by
  rw [finite_zonotope_eq_support_halfspaces]
  ext x
  simp only [projectionBodySet, Set.mem_ofPred_eq]
  constructor
  · intro hx u hu
    rw [← hbrightness u hu]
    exact hx u hu
  · intro hx u hu
    rw [hbrightness u hu]
    exact hx u hu

end ActualProjectionReduction

section VerticalExtrusion

variable {α : Type*}

def closedVerticalBand (s : Set α) (f g : α → ℝ) : Set (α × ℝ) :=
  {p | p.1 ∈ s ∧ p.2 ∈ Set.Icc (f p.1) (g p.1)}

def verticalExtrusion (K : Set (α × ℝ)) (τ : ℝ) : Set (α × ℝ) :=
  {p | ∃ q ∈ K, ∃ t ∈ Set.Icc (0 : ℝ) τ, p = (q.1, q.2 + t)}

/-- Actual set equality, before any measure calculation. -/
theorem vertical_extrusion_closed_band (s : Set α) (f g : α → ℝ) (τ : ℝ)
    (hτ : 0 ≤ τ) (hfg : ∀ x ∈ s, f x ≤ g x) :
    verticalExtrusion (closedVerticalBand s f g) τ =
      closedVerticalBand s f (fun x => g x + τ) := by
  ext p
  constructor
  · rintro ⟨q, hq, t, ht, rfl⟩
    exact ⟨hq.1, by dsimp; constructor <;> linarith [hq.2.1, hq.2.2, ht.1, ht.2]⟩
  · rintro ⟨hp, hlo, hhi⟩
    by_cases hg : p.2 ≤ g p.1
    · exact ⟨p, ⟨hp, hlo, hg⟩, 0, ⟨le_rfl, hτ⟩, by simp⟩
    · refine ⟨(p.1, g p.1), ⟨hp, hfg p.1 hp, le_rfl⟩, p.2 - g p.1, ?_, ?_⟩
      · constructor <;> linarith
      · ext <;> simp

variable [MeasurableSpace α]

theorem closed_vertical_band_measure (μ : Measure α) (s : Set α) (f g : α → ℝ)
    (hs : MeasurableSet s) (hf : Measurable f) (hg : Measurable g) :
    μ.prod volume (closedVerticalBand s f g) =
      ∫⁻ x in s, ENNReal.ofReal (g x - f x) ∂μ := by
  classical
  rw [Measure.prod_apply (show MeasurableSet (closedVerticalBand s f g) from
    measurableSet_region_between_cc hf hg hs)]
  have hsection : (fun x => volume (Prod.mk x ⁻¹' closedVerticalBand s f g)) =
      s.indicator (fun x => ENNReal.ofReal (g x - f x)) := by
    funext x
    by_cases hx : x ∈ s
    · simp only [closedVerticalBand, Set.preimage_ofPred_eq, hx, true_and,
        Set.indicator_of_mem hx]
      exact Real.volume_Icc
    · simp [closedVerticalBand, hx]
  rw [hsection, lintegral_indicator hs]

/-- The exact extrusion/Fubini increment for actual closed interval fibers.
No volume formula for a polytope or zonotope is assumed.
-/
theorem vertical_extrusion_volume (μ : Measure α) (s : Set α) (f g : α → ℝ)
    (τ : ℝ) (hs : MeasurableSet s) (hf : Measurable f) (hg : Measurable g)
    (hτ : 0 ≤ τ) (hfg : ∀ x ∈ s, f x ≤ g x) :
    μ.prod volume (verticalExtrusion (closedVerticalBand s f g) τ) =
      μ.prod volume (closedVerticalBand s f g) + ENNReal.ofReal τ * μ s := by
  rw [vertical_extrusion_closed_band s f g τ hτ hfg,
    closed_vertical_band_measure μ s f (fun x => g x + τ) hs hf (hg.add_const τ),
    closed_vertical_band_measure μ s f g hs hf hg]
  have hae : (fun x => ENNReal.ofReal (g x + τ - f x)) =ᵐ[μ.restrict s]
      (fun x => ENNReal.ofReal (g x - f x) + ENNReal.ofReal τ) := by
    filter_upwards [ae_restrict_mem hs] with x hx
    rw [show g x + τ - f x = (g x - f x) + τ by ring,
      ENNReal.ofReal_add (sub_nonneg.mpr (hfg x hx)) hτ]
  rw [lintegral_congr_ae hae, lintegral_add_right _ measurable_const,
    lintegral_const, Measure.restrict_apply_univ]

end VerticalExtrusion
end Entry005
