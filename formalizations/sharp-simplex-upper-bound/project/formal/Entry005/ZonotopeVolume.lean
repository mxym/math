import Entry005.ConeLawGeometry
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Normed.Module.Span

/-!
The actual extrusion identity for every compact convex body in product
coordinates.  The proof takes closed interval fibers pointwise and applies
Fubini to the measurable fiber-volume function; no endpoint measurability or
extrusion-volume identity is assumed.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Entry005

section CompactConvexExtrusion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- Fibers of an actual compact set are compact. -/
theorem compact_vertical_fiber {K : Set (E × ℝ)} (hK : IsCompact K) (x : E) :
    IsCompact (Prod.mk x ⁻¹' K) := by
  apply (hK.image continuous_snd).of_isClosed_subset
  · exact hK.isClosed.preimage (continuous_const.prodMk continuous_id)
  · intro t ht
    exact ⟨(x, t), ht, rfl⟩

/-- Nonempty fibers of an actual compact convex set are closed intervals. -/
theorem compact_convex_vertical_fiber {K : Set (E × ℝ)} (hK : IsCompact K)
    (hc : Convex ℝ K) {x : E} (hx : x ∈ Prod.fst '' K) :
    ∃ a b : ℝ, a ≤ b ∧ Prod.mk x ⁻¹' K = Set.Icc a b := by
  have hn : (Prod.mk x ⁻¹' K).Nonempty := by
    obtain ⟨p, hp, hpx⟩ := hx
    exact ⟨p.2, by simpa [← hpx] using hp⟩
  have hcv : Convex ℝ (Prod.mk x ⁻¹' K) := by
    intro a ha b hb c d hc' hd' hcd
    have hmem := hc ha hb hc' hd' hcd
    simpa [Set.mem_preimage, Prod.smul_mk, Prod.mk_add_mk,
      ← add_smul, hcd] using hmem
  have heq := eq_Icc_of_connected_compact (hcv.isConnected hn)
    (compact_vertical_fiber hK x)
  refine ⟨sInf (Prod.mk x ⁻¹' K), sSup (Prod.mk x ⁻¹' K), ?_, heq⟩
  rw [heq] at hn
  exact Set.nonempty_Icc.mp hn

omit [NormedSpace ℝ E] in
/-- Extrusion is a continuous image of the actual body times a closed segment. -/
theorem compact_vertical_extrusion {K : Set (E × ℝ)} (hK : IsCompact K) (τ : ℝ) :
    IsCompact (verticalExtrusion K τ) := by
  have heq : verticalExtrusion K τ =
      (fun p : (E × ℝ) × ℝ => (p.1.1, p.1.2 + p.2)) ''
        (K ×ˢ Set.Icc (0 : ℝ) τ) := by
    ext p
    constructor
    · rintro ⟨q, hq, t, ht, rfl⟩
      exact ⟨(q, t), ⟨hq, ht⟩, rfl⟩
    · rintro ⟨⟨q, t⟩, ⟨hq, ht⟩, rfl⟩
      exact ⟨q, hq, t, ht, rfl⟩
  rw [heq]
  exact (hK.prod isCompact_Icc).image
    ((continuous_fst.fst).prodMk (continuous_fst.snd.add continuous_snd))

/-- The gain in each nonempty vertical fiber is exactly the segment length. -/
theorem compact_convex_extrusion_fiber_volume {K : Set (E × ℝ)} (hK : IsCompact K)
    (hc : Convex ℝ K) (τ : ℝ) (hτ : 0 ≤ τ) (x : E) :
    volume (Prod.mk x ⁻¹' verticalExtrusion K τ) =
      volume (Prod.mk x ⁻¹' K) +
        (Prod.fst '' K).indicator (fun _ => ENNReal.ofReal τ) x := by
  classical
  by_cases hx : x ∈ Prod.fst '' K
  · obtain ⟨a, b, hab, hf⟩ := compact_convex_vertical_fiber hK hc hx
    have hext : Prod.mk x ⁻¹' verticalExtrusion K τ = Set.Icc a (b + τ) := by
      ext y
      constructor
      · rintro ⟨q, hq, t, ht, heq⟩
        have hqx : q.1 = x := by simpa using congrArg Prod.fst heq.symm
        have hqy : q.2 ∈ Set.Icc a b := by
          rw [← hf]
          simpa [← hqx] using hq
        have hy : y = q.2 + t := congrArg Prod.snd heq
        constructor <;> linarith [hqy.1, hqy.2, ht.1, ht.2]
      · rintro ⟨hya, hyb⟩
        by_cases hy : y ≤ b
        · refine ⟨(x, y), ?_, 0, ⟨le_rfl, hτ⟩, by simp⟩
          change y ∈ Prod.mk x ⁻¹' K
          rw [hf]
          exact ⟨hya, hy⟩
        · refine ⟨(x, b), ?_, y - b, ?_, ?_⟩
          · change b ∈ Prod.mk x ⁻¹' K
            rw [hf]
            exact ⟨hab, le_rfl⟩
          · constructor <;> linarith
          · ext <;> simp
    rw [hext, hf, Real.volume_Icc, Real.volume_Icc, Set.indicator_of_mem hx]
    rw [show b + τ - a = (b - a) + τ by ring,
      ENNReal.ofReal_add (sub_nonneg.mpr hab) hτ]
  · have hf : Prod.mk x ⁻¹' K = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro t ht
      exact hx ⟨(x, t), ht, rfl⟩
    have hext : Prod.mk x ⁻¹' verticalExtrusion K τ = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro y ⟨q, hq, t, ht, heq⟩
      exact hx ⟨q, hq, by simpa using congrArg Prod.fst heq.symm⟩
    simp [hext, hf, hx]

variable [MeasurableSpace E] [BorelSpace E]

/-- Exact actual-volume extrusion theorem, with arbitrary compact convex body
and arbitrary base measure.  Compactness supplies all measurability facts. -/
theorem compact_convex_vertical_extrusion_volume (μ : Measure E) {K : Set (E × ℝ)}
    (hK : IsCompact K) (hc : Convex ℝ K) (τ : ℝ) (hτ : 0 ≤ τ) :
    μ.prod volume (verticalExtrusion K τ) =
      μ.prod volume K + ENNReal.ofReal τ * μ (Prod.fst '' K) := by
  have hproj : MeasurableSet (Prod.fst '' K) := (hK.image continuous_fst).measurableSet
  rw [Measure.prod_apply (compact_vertical_extrusion hK τ).measurableSet,
    Measure.prod_apply hK.measurableSet]
  simp_rw [compact_convex_extrusion_fiber_volume hK hc τ hτ]
  rw [lintegral_add_right _ (measurable_const.indicator hproj),
    lintegral_indicator hproj, lintegral_const, Measure.restrict_apply_univ]

end CompactConvexExtrusion

section OrthogonalExtrusion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- An actual segment sum, parameterized by its length in a given direction. -/
def segmentExtrusion (K : Set E) (u : E) (τ : ℝ) : Set E :=
  {y | ∃ x ∈ K, ∃ t ∈ Set.Icc (0 : ℝ) τ, y = x + t • u}

/-- Orthogonal coordinates with the unit direction in the last coordinate. -/
def unitNormalLpCoordinates (u : E) (hu : ‖u‖ = 1) :
    E ≃ₗᵢ[ℝ] WithLp 2 ((ℝ ∙ u)ᗮ × ℝ) :=
  ((ℝ ∙ u).orthogonalDecomposition.trans
    (LinearIsometryEquiv.withLpProdComm 2 ℝ (ℝ ∙ u) (ℝ ∙ u)ᗮ)).trans
    (LinearIsometryEquiv.withLpProdCongr 2 (LinearIsometryEquiv.refl ℝ (ℝ ∙ u)ᗮ)
      (LinearIsometryEquiv.toSpanUnitSingleton u hu).symm)

def unitNormalCoordinates (u : E) (hu : ‖u‖ = 1) :
    E ≃L[ℝ] ((ℝ ∙ u)ᗮ × ℝ) :=
  (unitNormalLpCoordinates u hu).toContinuousLinearEquiv.trans
    (WithLp.prodContinuousLinearEquiv 2 ℝ (ℝ ∙ u)ᗮ ℝ)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem unit_normal_coordinates_fst (u : E) (hu : ‖u‖ = 1) (x : E) :
    (unitNormalCoordinates u hu x).1 = (ℝ ∙ u)ᗮ.orthogonalProjectionOnto x := by
  simp [unitNormalCoordinates, unitNormalLpCoordinates]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem unit_normal_coordinates_self (u : E) (hu : ‖u‖ = 1) :
    unitNormalCoordinates u hu u = (0, 1) := by
  have huP : u ∈ ℝ ∙ u := Submodule.mem_span_singleton_self u
  have horth : (ℝ ∙ u)ᗮ.orthogonalProjectionOnto u = 0 := by
    apply Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr
    simpa only [Submodule.orthogonal_orthogonal] using huP
  have hproj : (ℝ ∙ u).orthogonalProjectionOnto u =
      LinearIsometryEquiv.toSpanUnitSingleton u hu 1 := by
    rw [LinearIsometryEquiv.toSpanUnitSingleton_apply]
    simpa using (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self
      (⟨u, huP⟩ : ℝ ∙ u))
  apply Prod.ext
  · exact (unit_normal_coordinates_fst u hu u).trans horth
  · simp [unitNormalCoordinates, unitNormalLpCoordinates, hproj]
    simpa using (LinearIsometryEquiv.toSpanUnitSingleton u hu).symm_apply_apply (1 : ℝ)

/-- These orthogonal coordinates preserve the actual canonical volume. -/
theorem unit_normal_coordinates_measurePreserving (u : E) (hu : ‖u‖ = 1) :
    @MeasurePreserving E ((ℝ ∙ u)ᗮ × ℝ) ‹MeasurableSpace E› inferInstance
      (unitNormalCoordinates u hu) volume (volume.prod volume) := by
  exact (WithLp.volume_preserving_ofLp (ℝ ∙ u)ᗮ ℝ).comp
    (unitNormalLpCoordinates u hu).measurePreserving

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem compact_segment_extrusion {K : Set E} (hK : IsCompact K) (u : E) (τ : ℝ) :
    IsCompact (segmentExtrusion K u τ) := by
  have heq : segmentExtrusion K u τ =
      (fun p : E × ℝ => p.1 + p.2 • u) '' (K ×ˢ Set.Icc (0 : ℝ) τ) := by
    ext p
    constructor
    · rintro ⟨q, hq, t, ht, rfl⟩
      exact ⟨(q, t), ⟨hq, ht⟩, rfl⟩
    · rintro ⟨⟨q, t⟩, ⟨hq, ht⟩, rfl⟩
      exact ⟨q, hq, t, ht, rfl⟩
  rw [heq]
  exact (hK.prod isCompact_Icc).image
    (continuous_fst.add (continuous_snd.smul continuous_const))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem unit_normal_coordinates_extrusion (K : Set E) (u : E) (hu : ‖u‖ = 1)
    (τ : ℝ) :
    unitNormalCoordinates u hu '' segmentExtrusion K u τ =
      verticalExtrusion (unitNormalCoordinates u hu '' K) τ := by
  ext p
  constructor
  · rintro ⟨y, ⟨x, hx, t, ht, rfl⟩, rfl⟩
    refine ⟨unitNormalCoordinates u hu x, ⟨x, hx, rfl⟩, t, ht, ?_⟩
    simp [Prod.ext_iff, map_add, map_smul, unit_normal_coordinates_self,
      Prod.smul_mk]
  · rintro ⟨q, ⟨x, hx, rfl⟩, t, ht, rfl⟩
    refine ⟨x + t • u, ⟨x, hx, t, ht, rfl⟩, ?_⟩
    simp [Prod.ext_iff, map_add, map_smul, unit_normal_coordinates_self,
      Prod.smul_mk]

theorem unit_normal_coordinates_volume (u : E) (hu : ‖u‖ = 1)
    {K : Set E} (hK : IsCompact K) :
    volume K = volume.prod volume (unitNormalCoordinates u hu '' K) := by
  have heq := (unit_normal_coordinates_measurePreserving u hu).measure_preimage
    (hK.image (unitNormalCoordinates u hu).continuous).measurableSet.nullMeasurableSet
  simpa only [Set.preimage_image_eq K (unitNormalCoordinates u hu).injective] using heq

/-- The actual Euclidean extrusion formula for a unit direction.  Both
orthogonal coordinates and volume preservation are proved above. -/
theorem compact_convex_unit_extrusion_volume {K : Set E} (hK : IsCompact K)
    (hc : Convex ℝ K) (u : E) (hu : ‖u‖ = 1) (τ : ℝ) (hτ : 0 ≤ τ) :
    volume (segmentExtrusion K u τ) =
      volume K + ENNReal.ofReal τ *
        volume ((ℝ ∙ u)ᗮ.orthogonalProjectionOnto '' K) := by
  rw [unit_normal_coordinates_volume u hu (compact_segment_extrusion hK u τ),
    unit_normal_coordinates_extrusion,
    compact_convex_vertical_extrusion_volume volume
      (hK.image (unitNormalCoordinates u hu).continuous)
      (hc.linear_image (unitNormalCoordinates u hu).toLinearMap) τ hτ,
    ← unit_normal_coordinates_volume u hu hK]
  have hfun : Prod.fst ∘ unitNormalCoordinates u hu =
      (ℝ ∙ u)ᗮ.orthogonalProjectionOnto := by
    funext x
    exact unit_normal_coordinates_fst u hu x
  rw [← Set.image_comp, hfun]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem segment_extrusion_rescale (K : Set E) (u : E) (τ c : ℝ) (hc : 0 < c) :
    segmentExtrusion K (c • u) τ = segmentExtrusion K u (τ * c) := by
  ext y
  constructor
  · rintro ⟨x, hx, t, ht, rfl⟩
    refine ⟨x, hx, t * c, ⟨mul_nonneg ht.1 hc.le,
      mul_le_mul_of_nonneg_right ht.2 hc.le⟩, ?_⟩
    rw [smul_smul]
  · rintro ⟨x, hx, t, ht, rfl⟩
    refine ⟨x, hx, t / c, ⟨div_nonneg ht.1 hc.le,
      (div_le_iff₀ hc).mpr ht.2⟩, ?_⟩
    rw [smul_smul, div_mul_cancel₀ _ hc.ne']

/-- The actual coordinate-free segment extrusion formula, including the zero
direction and lower-dimensional compact convex bodies. -/
theorem compact_convex_extrusion_volume {K : Set E} (hK : IsCompact K)
    (hc : Convex ℝ K) (v : E) (τ : ℝ) (hτ : 0 ≤ τ) :
    volume (segmentExtrusion K v τ) =
      volume K + ENNReal.ofReal (τ * ‖v‖) *
        volume ((ℝ ∙ v)ᗮ.orthogonalProjectionOnto '' K) := by
  by_cases hv : v = 0
  · have heq : segmentExtrusion K v τ = K := by
      subst v
      ext y
      constructor
      · rintro ⟨x, hx, t, ht, rfl⟩
        simpa using hx
      · intro hy
        exact ⟨y, hy, 0, ⟨le_rfl, hτ⟩, by simp⟩
    rw [heq]
    simp [hv]
  · let u := ‖v‖⁻¹ • v
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hu : ‖u‖ = 1 := by simp [u, norm_smul, hn.ne']
    have hvu : ‖v‖ • u = v := by simp [u, smul_smul, hn.ne']
    have hspan : ℝ ∙ u = ℝ ∙ v :=
      Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr (inv_ne_zero hn.ne')) v
    have heq : segmentExtrusion K v τ = segmentExtrusion K u (τ * ‖v‖) := by
      conv_lhs => rw [← hvu]
      exact segment_extrusion_rescale K u τ ‖v‖ hn
    have hp : volume ((ℝ ∙ u)ᗮ.orthogonalProjectionOnto '' K) =
        volume ((ℝ ∙ v)ᗮ.orthogonalProjectionOnto '' K) :=
      congrArg (fun P : Submodule ℝ E => volume (Pᗮ.orthogonalProjectionOnto '' K)) hspan
    rw [heq, compact_convex_unit_extrusion_volume hK hc u hu (τ * ‖v‖)
      (mul_nonneg hτ hn.le), hp]

end OrthogonalExtrusion

section ZonotopeRecursion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Projection and every other linear image commute with the actual segment sum. -/
theorem finite_zonotope_linear_image {ι F : Type*} [Fintype ι]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] (g : ι → E) (f : E →ₗ[ℝ] F) :
    f '' finiteZonotope g = finiteZonotope (fun i => f (g i)) := by
  ext y
  constructor
  · rintro ⟨x, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨t, ht, by simp⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨∑ i, t i • g i, ⟨t, ht, rfl⟩, ?_⟩
    simp

def symmetricSegmentExtrusion (K : Set E) (v : E) : Set E :=
  {y | ∃ x ∈ K, ∃ t ∈ Set.Icc (-1 : ℝ) 1, y = x + t • v}

/-- Adding one actual zonotope generator is symmetric segment extrusion. -/
theorem finite_zonotope_cons {m : ℕ} (g : Fin m → E) (v : E) :
    finiteZonotope (Fin.cons v g) = symmetricSegmentExtrusion (finiteZonotope g) v := by
  ext y
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨∑ i, a i.succ • g i, ⟨fun i => a i.succ, fun i => ha i.succ, rfl⟩,
      a 0, ha 0, ?_⟩
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    exact add_comm _ _
  · rintro ⟨x, ⟨a, ha, rfl⟩, t, ht, rfl⟩
    refine ⟨Fin.cons t a, ?_, ?_⟩
    · intro i
      refine Fin.cases ht (fun j => ?_) i
      simpa using ha j
    · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      exact add_comm _ _

theorem symmetric_segment_extrusion_eq_preimage (K : Set E) (v : E) :
    symmetricSegmentExtrusion K v =
      (fun y => v + y) ⁻¹' segmentExtrusion K v 2 := by
  ext y
  constructor
  · rintro ⟨x, hx, t, ht, rfl⟩
    refine ⟨x, hx, t + 1, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    rw [add_smul, one_smul]
    abel
  · rintro ⟨x, hx, t, ht, hy⟩
    refine ⟨x, hx, t - 1, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    calc
      y = -v + (v + y) := by abel
      _ = -v + (x + t • v) := congrArg (fun z => -v + z) hy
      _ = x + (t - 1) • v := by rw [sub_smul, one_smul]; abel

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Exact geometric recurrence for actual finite zonotope volume. -/
theorem finite_zonotope_volume_cons {m : ℕ} (g : Fin m → E) (v : E) :
    volume (finiteZonotope (Fin.cons v g)) =
      volume (finiteZonotope g) + ENNReal.ofReal (2 * ‖v‖) *
        volume ((ℝ ∙ v)ᗮ.orthogonalProjectionOnto '' finiteZonotope g) := by
  rw [finite_zonotope_cons, symmetric_segment_extrusion_eq_preimage,
    measure_preimage_add, compact_convex_extrusion_volume
      (finite_zonotope_compact g) (finite_zonotope_convex g) v 2 (by norm_num)]

/-- The same recurrence in the real-valued volume convention of the targets. -/
theorem finite_zonotope_volume_cons_toReal {m : ℕ} (g : Fin m → E) (v : E) :
    (volume (finiteZonotope (Fin.cons v g))).toReal =
      (volume (finiteZonotope g)).toReal + (2 * ‖v‖) *
        (volume ((ℝ ∙ v)ᗮ.orthogonalProjectionOnto '' finiteZonotope g)).toReal := by
  rw [finite_zonotope_volume_cons,
    ENNReal.toReal_add (finite_zonotope_compact g).measure_lt_top.ne
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        ((finite_zonotope_compact g).image
          (ℝ ∙ v)ᗮ.orthogonalProjectionOnto.continuous).measure_lt_top.ne),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

/-- The recurrence with the projection itself expressed as an actual finite
zonotope in the lower-dimensional orthogonal subspace. -/
theorem finite_zonotope_volume_cons_projected {m : ℕ} (g : Fin m → E) (v : E) :
    (volume (finiteZonotope (Fin.cons v g))).toReal =
      (volume (finiteZonotope g)).toReal + (2 * ‖v‖) *
        (volume (finiteZonotope (fun i => (ℝ ∙ v)ᗮ.orthogonalProjectionOnto (g i)))).toReal := by
  rw [finite_zonotope_volume_cons_toReal]
  have heq : (ℝ ∙ v)ᗮ.orthogonalProjectionOnto '' finiteZonotope g =
      finiteZonotope (fun i => (ℝ ∙ v)ᗮ.orthogonalProjectionOnto (g i)) :=
    finite_zonotope_linear_image g (ℝ ∙ v)ᗮ.orthogonalProjectionOnto.toLinearMap
  rw [heq]

end ZonotopeRecursion

section RealZonotope

/-- The full actual one-dimensional zonotope set formula. -/
theorem finite_zonotope_real_eq_interval {ι : Type*} [Fintype ι] (g : ι → ℝ) :
    finiteZonotope g = Set.Icc (-(∑ i, |g i|)) (∑ i, |g i|) := by
  have hnonneg : 0 ≤ ∑ i, |g i| := Finset.sum_nonneg (fun i _ => abs_nonneg (g i))
  have hhi : (∑ i, |g i|) ∈ finiteZonotope g := by
    obtain ⟨x, hx, heq⟩ := finite_zonotope_support_attained g 1
    have hx' : x = ∑ i, |g i| := by simpa [RCLike.inner_apply] using heq
    rwa [hx'] at hx
  have hlo : (-(∑ i, |g i|)) ∈ finiteZonotope g := by
    obtain ⟨x, hx, heq⟩ := finite_zonotope_support_attained g (-1)
    have hx' : -x = ∑ i, |g i| := by simpa [RCLike.inner_apply] using heq
    have hx'' : x = -(∑ i, |g i|) := by linarith
    rwa [hx''] at hx
  ext x
  constructor
  · intro hx
    have hupper := finite_zonotope_support_bound g 1 x hx
    have hlower := finite_zonotope_support_bound g (-1) x hx
    simp only [RCLike.inner_apply, map_one, mul_one, map_neg, mul_neg,
      abs_neg] at hupper hlower
    constructor <;> linarith
  · intro hx
    apply (finite_zonotope_convex g).segment_subset hlo hhi
    rwa [segment_eq_Icc (by linarith)]

/-- The full actual one-dimensional determinant-sum volume formula. -/
theorem finite_zonotope_real_volume {ι : Type*} [Fintype ι] (g : ι → ℝ) :
    (volume (finiteZonotope g)).toReal = 2 * ∑ i, |g i| := by
  have hnonneg : 0 ≤ ∑ i, |g i| := Finset.sum_nonneg (fun i _ => abs_nonneg (g i))
  rw [finite_zonotope_real_eq_interval, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith)]
  ring

end RealZonotope
end Entry005
