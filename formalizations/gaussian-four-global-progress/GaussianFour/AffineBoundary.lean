import GaussianPolyhedralGraphFlux
import GaussianTail
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Continuity of actual Gaussian integrals over moving finite affine masks.
Zero normals are allowed when their constant inequalities are nonzero. -/
open MeasureTheory ProbabilityTheory Filter Set
open scoped RealInnerProductSpace Topology
open GaussianMeasureBridge
namespace GaussianFour
variable {d k : ℕ}

def affineMask (s : Finset (Fin k)) (a : Fin k → Space d) (b : Fin k → ℝ) :
    Set (Space d) := {x | ∀ i ∈ s, b i < ⟪a i, x⟫}

lemma measurableSet_affineMask (s : Finset (Fin k))
    (a : Fin k → Space d) (b : Fin k → ℝ) : MeasurableSet (affineMask s a b) := by
  unfold affineMask
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
    measurableSet_lt measurable_const (by fun_prop)

/-- Nonzero affine functionals have Gaussian-null zero sets. -/
lemma ae_affine_ne (a : Space d) (b : ℝ) (h : a ≠ 0 ∨ b ≠ 0) :
    ∀ᵐ x ∂gaussian d, ⟪a, x⟫ ≠ b := by
  by_cases ha : a = 0
  · have hb : b ≠ 0 := h.resolve_left (not_not.mpr ha)
    exact ae_of_all _ fun x => by simpa [ha] using Ne.symm hb
  · rw [ae_iff]
    simpa only [not_not] using gaussian_hyperplane_null a ha b

noncomputable def affineDensityIntegral (s : Finset (Fin k))
    (a : Fin k → Space d) (b : Fin k → ℝ) (n : Space d) (c : ℝ) : ℝ :=
  ∫ x in affineMask s a b, standardDensity (⟪n, x⟫ - c) ∂gaussian d

lemma integrable_affineDensity (s : Finset (Fin k))
    (a : Fin k → Space d) (b : Fin k → ℝ) (n : Space d) (c : ℝ) :
    Integrable ((affineMask s a b).indicator
      (fun x => standardDensity (⟪n, x⟫ - c))) (gaussian d) :=
  (integrable_standardDensity_comp (gaussian d) _ (by fun_prop)).indicator
    (measurableSet_affineMask s a b)

variable {T : Type*} [TopologicalSpace T] [FirstCountableTopology T]

lemma eventually_affineMask_iff (s : Finset (Fin k))
    (a : T → Fin k → Space d) (b : T → Fin k → ℝ) (z : T) (x : Space d)
    (ha : ∀ i ∈ s, ContinuousAt (fun t => a t i) z)
    (hb : ∀ i ∈ s, ContinuousAt (fun t => b t i) z)
    (hx : ∀ i ∈ s, ⟪a z i, x⟫ ≠ b z i) :
    ∀ᶠ t in 𝓝 z, (x ∈ affineMask s (a t) (b t)) ↔
      (x ∈ affineMask s (a z) (b z)) := by
  have he : ∀ᶠ t in 𝓝 z, ∀ i, i ∈ s →
      ((b t i < ⟪a t i, x⟫) ↔ (b z i < ⟪a z i, x⟫)) := by
    apply eventually_all.mpr
    intro i
    by_cases hi : i ∈ s
    · have hc : ContinuousAt (fun t => ⟪a t i, x⟫) z :=
        (ha i hi).inner continuousAt_const
      by_cases hlt : b z i < ⟪a z i, x⟫
      · exact ((hb i hi).eventually_lt hc hlt).mono fun t ht _ => iff_of_true ht hlt
      · have hgt : ⟪a z i, x⟫ < b z i :=
          lt_of_le_of_ne (le_of_not_gt hlt) (hx i hi)
        exact (hc.eventually_lt (hb i hi) hgt).mono fun t ht _ =>
          iff_of_false (not_lt_of_ge ht.le) hlt
    · exact Eventually.of_forall fun t h => False.elim (hi h)
  filter_upwards [he] with t ht
  exact forall_congr' fun i => forall_congr' fun hi => ht i hi

/-- Dominated convergence for moving affine graph facets, allowing singular
linear parts. All integrals are against the actual standard Gaussian measure. -/
theorem continuousAt_affineDensityIntegral (s : Finset (Fin k))
    (a : T → Fin k → Space d) (b : T → Fin k → ℝ)
    (n : T → Space d) (c : T → ℝ) (z : T)
    (ha : ∀ i ∈ s, ContinuousAt (fun t => a t i) z)
    (hb : ∀ i ∈ s, ContinuousAt (fun t => b t i) z)
    (hn : ContinuousAt n z) (hc : ContinuousAt c z)
    (hboundary : ∀ i ∈ s, a z i ≠ 0 ∨ b z i ≠ 0) :
    ContinuousAt (fun t => affineDensityIntegral s (a t) (b t) (n t) (c t)) z := by
  have heq : (fun t => affineDensityIntegral s (a t) (b t) (n t) (c t)) =
      (fun t => ∫ x, (affineMask s (a t) (b t)).indicator
        (fun x => standardDensity (⟪n t, x⟫ - c t)) x ∂gaussian d) := by
    funext t
    exact (integral_indicator (measurableSet_affineMask s (a t) (b t))).symm
  rw [heq]
  apply continuousAt_of_dominated (bound := fun _ : Space d => standardDensity 0)
  · exact Eventually.of_forall fun t =>
      (integrable_affineDensity s (a t) (b t) (n t) (c t)).aestronglyMeasurable
  · exact Eventually.of_forall fun t => ae_of_all _ fun x => by
      by_cases hx : x ∈ affineMask s (a t) (b t)
      · rw [indicator_of_mem hx, Real.norm_eq_abs, abs_of_pos (standardDensity_pos _)]
        exact standardDensity_le_zero _
      · simp only [indicator_of_notMem hx, norm_zero]
        exact (standardDensity_pos 0).le
  · exact integrable_const _
  · have hne : ∀ᵐ x ∂gaussian d, ∀ i, i ∈ s → ⟪a z i, x⟫ ≠ b z i := by
      apply ae_all_iff.mpr
      intro i
      by_cases hi : i ∈ s
      · exact (ae_affine_ne _ _ (hboundary i hi)).mono fun x hx _ => hx
      · exact ae_of_all _ fun x h => False.elim (hi h)
    filter_upwards [hne] with x hx
    have hev := eventually_affineMask_iff s a b z x ha hb hx
    have hw : ContinuousAt (fun t => standardDensity (⟪n t, x⟫ - c t)) z :=
      continuous_standardDensity.continuousAt.comp ((hn.inner continuousAt_const).sub hc)
    by_cases hmem : x ∈ affineMask s (a z) (b z)
    · apply hw.congr_of_eventuallyEq
      filter_upwards [hev] with t ht
      exact indicator_of_mem (ht.mpr hmem) _
    · apply continuousAt_const.congr_of_eventuallyEq
      filter_upwards [hev] with t ht
      exact indicator_of_notMem (fun h => hmem (ht.mp h)) _

end GaussianFour
