import GaussianClusterNullRepair
import GaussianBVClusterUpperLimit
import GaussianBVMinimizingSequence

/-! An actual cellwise indicator-L1 limit of a minimizing sequence gives a
genuine equal-mass minimizing cluster, after a proved null-set repair. The
existence of a convergent subsequence is the explicit remaining compactness
obligation, not an axiom or a hidden hypothesis on Gaussian measure. -/
open MeasureTheory ProbabilityTheory Module Set Filter
open scoped Topology ENNReal ContDiff RealInnerProductSpace
namespace GaussianMeasureBridge

theorem exists_balanced_BV_minimizer_of_cellwise_indicatorL1_limit
    (d : ℕ) (C : ℕ → BalancedGaussianCluster (d+1) (d+2))
    (hper : Tendsto (fun n => (C n).perimeter) atTop (𝓝 (balancedGaussianBVProfile d)))
    (S : Fin (d+2) → Set (Space (d+1))) (hS : ∀ i,MeasurableSet (S i))
    (hdist : ∀ i,Tendsto (fun n => gaussianIndicatorL1Distance ((C n).cell i) (S i)) atTop (𝓝 0)) :
    ∃ D : BalancedGaussianCluster (d+1) (d+2),
      D.perimeter=balancedGaussianBVProfile d ∧
      ∀ i,∀ᵐ x ∂gaussian (d+1),x ∈ D.cell i ↔ x ∈ S i := by
  have hsum := ae_sum_indicator_of_cluster_indicatorL1_limit C S hS hdist
  have hmass (i : Fin (d+2)) : (gaussian (d+1)).real (S i)=uniformMass (d+2) i :=
    gaussian_fixed_mass_preserved_by_indicatorL1 (S i) (fun n => (C n).cell i)
      (uniformMass (d+2) i) (hS i) (fun n => (C n).measurable i) (hdist i) (fun n => (C n).mass i)
  let D := repairedBalancedGaussianCluster S hS hsum hmass
  have hAE (i : Fin (d+2)) : ∀ᵐ x ∂gaussian (d+1),x ∈ D.cell i ↔ x ∈ S i :=
    firstLabelCell_ae_eq S hsum i
  have hcell (i : Fin (d+2)) : gaussianBVPerimeter (D.cell i)=gaussianBVPerimeter (S i) :=
    gaussianBVPerimeter_congr_ae _ _ (D.measurable i) (hS i) (hAE i)
  have hperD : D.perimeter=(∑ i,gaussianBVPerimeter (S i))/2 := by
    unfold BalancedGaussianCluster.perimeter
    simp_rw [hcell]
  refine ⟨D,le_antisymm ?_ ?_,hAE⟩
  · rw [hperD]
    exact gaussian_total_BV_upper_limit_under_indicatorL1 S (fun n => (C n).cell)
      (fun n => (C n).perimeter) (balancedGaussianBVProfile d) hS
      (fun n => (C n).measurable) hdist (fun _ => le_rfl) hper
  · exact iInf_le (fun E : BalancedGaussianCluster (d+1) (d+2) => E.perimeter) D

end GaussianMeasureBridge
