import BapatPeakToEndpoint
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Topology

namespace BapatRealExistence
noncomputable section
variable {K : Type*} [MetricSpace K] [CompactSpace K] [Nonempty K]
  [MeasurableSpace K] [BorelSpace K]

def empiricalAverage (u : ℕ → K) (n : ℕ) (f : K → ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, f (u i)

/-- Countably many actual integrable tests hold simultaneously along one sequence. -/
theorem exists_cloud_countable_tests (μ : Measure K) [IsProbabilityMeasure μ]
    (f : ℕ → C(K, ℝ)) :
    ∃ u : ℕ → K, ∀ k, Tendsto (fun n => empiricalAverage u n (f k)) atTop
      (𝓝 (∫ x, f k x ∂μ)) := by
  let P : Measure (ℕ → K) := infinitePi (fun _ : ℕ => μ)
  have htest (k : ℕ) : ∀ᵐ u ∂P, Tendsto
      (fun n => empiricalAverage u n (f k)) atTop (𝓝 (∫ x, f k x ∂μ)) := by
    have hm : Measurable (f k) := (f k).continuous.measurable
    have hlaw (i : ℕ) : IdentDistrib (fun u : ℕ → K => f k (u i)) (f k) P μ := by
      refine ⟨(hm.comp (measurable_pi_apply i)).aemeasurable, hm.aemeasurable, ?_⟩
      dsimp [P]
      change Measure.map ((f k) ∘ (fun u : ℕ → K => u i)) (infinitePi (fun _ : ℕ => μ)) = _
      rw [← Measure.map_map hm (measurable_pi_apply i), infinitePi_map_eval]
    have hint : Integrable (fun u : ℕ → K => f k (u 0)) P :=
      (hlaw 0).integrable_iff.mpr
        ((f k).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    have hindep := iIndepFun_infinitePi (P := fun _ : ℕ => μ) (X := fun _ => f k)
      (fun _ => hm)
    have h := strong_law_ae (fun i (u : ℕ → K) => f k (u i)) hint
      (fun i j hij => hindep.indepFun hij) (fun i => (hlaw i).trans (hlaw 0).symm)
    rw [(hlaw 0).integral_eq] at h
    simpa only [empiricalAverage, smul_eq_mul] using h
  exact (ae_all_iff.mpr htest).exists

/-- Uniform approximation controls empirical means independently of sample size. -/
theorem empiricalAverage_dist_le (u : ℕ → K) (n : ℕ) (f g : C(K, ℝ)) :
    dist (empiricalAverage u n f) (empiricalAverage u n g) ≤ dist f g := by
  by_cases hn : n = 0
  · subst n; simp [empiricalAverage]
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  rw [dist_eq_norm, empiricalAverage, empiricalAverage, ← mul_sub, ← Finset.sum_sub_distrib,
    norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr hnpos.le)]
  calc
    _ ≤ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ‖f (u i) - g (u i)‖ := by
      exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hnpos.le)
    _ ≤ (n : ℝ)⁻¹ * ∑ _i ∈ Finset.range n, dist f g := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hnpos.le)
      apply Finset.sum_le_sum
      intro i hi
      simpa only [dist_eq_norm] using (ContinuousMap.dist_apply_le_dist (f := f) (g := g) (u i))
    _ = dist f g := by simp [hn, mul_assoc]

theorem integral_continuous_dist_le (μ : Measure K) [IsProbabilityMeasure μ]
    (f g : C(K, ℝ)) : dist (∫ x, f x ∂μ) (∫ x, g x ∂μ) ≤ dist f g := by
  rw [dist_eq_norm, ← integral_sub
    (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  have hb : ∀ x : K, ‖f x - g x‖ ≤ dist f g := by
    intro x
    simpa only [dist_eq_norm] using (ContinuousMap.dist_apply_le_dist (f := f) (g := g) x)
  simpa using norm_integral_le_of_norm_le_const (μ := μ) (Filter.Eventually.of_forall hb)

/-- Every compact metric probability space admits a deterministic equidistributed sequence. -/
theorem exists_equidistributed_cloud (μ : Measure K) [IsProbabilityMeasure μ] :
    ∃ u : ℕ → K, ∀ f : C(K, ℝ), Tendsto (fun n => empiricalAverage u n f) atTop
      (𝓝 (∫ x, f x ∂μ)) := by
  obtain ⟨g, hg⟩ := TopologicalSpace.exists_dense_seq C(K, ℝ)
  obtain ⟨u, hu⟩ := exists_cloud_countable_tests μ g
  refine ⟨u, fun f => Metric.tendsto_atTop.mpr ?_⟩
  intro ε hε
  obtain ⟨k, hk⟩ := hg.exists_dist_lt f (by positivity : 0 < ε/3)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hu k) (ε/3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have ha := empiricalAverage_dist_le u n f (g k)
  have hb := integral_continuous_dist_le μ (g k) f
  have hc := hN n hn
  have ht := dist_triangle4 (empiricalAverage u n f) (empiricalAverage u n (g k))
    (∫ x, g k x ∂μ) (∫ x, f x ∂μ)
  rw [dist_comm (g k) f] at hb
  linarith

abbrev RealUnitSphere4 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

instance : Nonempty RealUnitSphere4 :=
  ⟨⟨EuclideanSpace.single (0 : Fin 4) (1 : ℝ), by simp⟩⟩

/-- The actual real sphere has an equidistributed cloud for its normalized Haar measure. -/
theorem exists_real_sphere_cloud :
    ∃ u : ℕ → RealUnitSphere4, ∀ f : C(RealUnitSphere4, ℝ),
      Tendsto (fun n => empiricalAverage u n f) atTop
        (𝓝 (∫ x, f x ∂normalizedSphere (volume : Measure (EuclideanSpace ℝ (Fin 4))))) :=
  exists_equidistributed_cloud _

end
end BapatRealExistence
