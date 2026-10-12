import GaussianIndicatorMassLimit
import GaussianBVComparisonInterface

/-! Actual cellwise indicator-L1 limits of measurable Gaussian clusters
retain the partition simplex constraint almost everywhere. This concerns
limits already supplied; it does not assert BV compactness. -/
open MeasureTheory ProbabilityTheory Module Set Filter
open scoped Topology ENNReal ContDiff RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d k : ℕ}

lemma BalancedGaussianCluster.ae_sum_indicator (C : BalancedGaussianCluster d k) :
    ∀ᵐ x ∂gaussian d,∑ i,(C.cell i).indicator (fun _ => (1 : ℝ)) x=1 := by
  classical
  filter_upwards [C.cover] with x hx
  obtain ⟨r,hr⟩ := hx
  have hnot (j : Fin k) (hj : j ≠ r) : x ∉ C.cell j := fun h =>
    Set.disjoint_left.mp (C.disjoint j r hj) h hr
  rw [Finset.sum_eq_single r]
  · simp only [Set.indicator_of_mem hr]
  · intro j _ hj
    simp only [Set.indicator_of_notMem (hnot j hj)]
  · simp

theorem ae_sum_indicator_of_cluster_indicatorL1_limit
    (C : ℕ → BalancedGaussianCluster d k) (S : Fin k → Set (Space d))
    (hS : ∀ i,MeasurableSet (S i))
    (hdist : ∀ i,Tendsto (fun n => gaussianIndicatorL1Distance ((C n).cell i) (S i)) atTop (𝓝 0)) :
    ∀ᵐ x ∂gaussian d,∑ i,(S i).indicator (fun _ => (1 : ℝ)) x=1 := by
  have hSi (i : Fin k) : Integrable ((S i).indicator (fun _ => (1 : ℝ))) (gaussian d) :=
    (integrable_const (1 : ℝ)).indicator (hS i)
  have he : Integrable (fun x => ‖(∑ i,(S i).indicator (fun _ => (1 : ℝ)) x)-1‖) (gaussian d) :=
    ((integrable_finsetSum Finset.univ (fun i _ => hSi i)).sub (integrable_const (1 : ℝ))).norm
  have hi (n : ℕ) : (∫ x,‖(∑ i,(S i).indicator (fun _ => (1 : ℝ)) x)-1‖ ∂gaussian d) ≤
      ∑ i,gaussianIndicatorL1Distance ((C n).cell i) (S i) := by
    have hnorm (i : Fin k) : Integrable (fun x => ‖((C n).cell i).indicator (fun _ => (1 : ℝ)) x-
        (S i).indicator (fun _ => (1 : ℝ)) x‖) (gaussian d) :=
      gaussianIndicatorL1_integrable _ _ ((C n).measurable i) (hS i)
    have hh : (∫ x,‖(∑ i,(S i).indicator (fun _ => (1 : ℝ)) x)-1‖ ∂gaussian d) ≤
        ∫ x,(∑ i,‖((C n).cell i).indicator (fun _ => (1 : ℝ)) x-
          (S i).indicator (fun _ => (1 : ℝ)) x‖) ∂gaussian d := by
      apply integral_mono_ae he (integrable_finsetSum Finset.univ (fun i _ => hnorm i))
      filter_upwards [(C n).ae_sum_indicator] with x hx
      calc
        _ = ‖1-(∑ i,(S i).indicator (fun _ => (1 : ℝ)) x)‖ := norm_sub_rev _ _
        _ = ‖∑ i,(((C n).cell i).indicator (fun _ => (1 : ℝ)) x-
            (S i).indicator (fun _ => (1 : ℝ)) x)‖ := by
          rw [Finset.sum_sub_distrib,hx]
        _ ≤ _ := norm_sum_le _ _
    apply hh.trans_eq
    rw [integral_finsetSum Finset.univ (fun i _ => hnorm i)]
    rfl
  have ht : Tendsto (fun n => ∑ i,gaussianIndicatorL1Distance ((C n).cell i) (S i)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun i _ => hdist i)
  have hz : (∫ x,‖(∑ i,(S i).indicator (fun _ => (1 : ℝ)) x)-1‖ ∂gaussian d)=0 := by
    have hle := le_of_tendsto_of_tendsto tendsto_const_nhds ht (Eventually.of_forall hi)
    exact le_antisymm hle (integral_nonneg (fun _ => norm_nonneg _))
  have hae := (integral_eq_zero_iff_of_nonneg (fun _ => norm_nonneg _) he).mp hz
  filter_upwards [hae] with x hx
  change ‖(∑ i,(S i).indicator (fun _ => (1 : ℝ)) x)-1‖=0 at hx
  exact sub_eq_zero.mp (norm_eq_zero.mp hx)

end GaussianMeasureBridge
