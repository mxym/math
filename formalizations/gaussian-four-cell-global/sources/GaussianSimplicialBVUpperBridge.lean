import GaussianSimplicialGradientUpperLimit
import GaussianBVUpperLimit
import GaussianBVComparisonInterface

/-! Unconditional upper bridge from the genuine variational Gaussian BV
perimeter to the genuine closed-ball erosion perimeter, for every full
simplicial winning cell at arbitrary prices. The proof uses smooth products,
dual normal directions and actual Gaussian first moments. -/
open MeasureTheory ProbabilityTheory Module Set Filter
open scoped Topology ENNReal ContDiff RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d : ℕ}

theorem simplicial_zero_cell_BV_upper
    (v : Fin (d+2) → Space (d+1)) (b : Fin (d+2) → ℝ)
    (B : Basis (Fin (d+1)) ℝ (Space (d+1))) (hB : ∀ l,B l=v 0-v l.succ) :
    gaussianBVPerimeter (winningCell v b 0) ≤
      ENNReal.ofReal (gaussianInnerPerimeter (winningCell v b 0)) := by
  obtain ⟨w,_,hf⟩ := gaussian_simplicial_cell_positive_flux v b B hB
  have hd := simplicial_cell_erosion_derivative v b B hB w hf
  have hper : gaussianInnerPerimeter (winningCell v b 0)=∑ l,w l*‖v 0-v l.succ‖ := by
    rw [gaussianInnerPerimeter,hd.derivWithin (uniqueDiffOn_Ici 0 0 self_mem_Ici),neg_neg]
  rw [hper]
  apply gaussianBV_upper_of_smooth_upper_limit (winningCell v b 0)
    (measurableSet_winningCell v b 0) (smoothWinningApprox v b 0)
    (simplicialGradientUpper v b) (∑ l,w l*‖v 0-v l.succ‖)
  · exact smoothWinningApprox_contDiff v b 0
  · exact smoothWinningApprox_bounds v b 0
  · exact ae_of_all _ fun x => smoothWinningApprox_tendsto v b 0 x
  · exact smoothWinningApprox_gradient_integrable v b 0
  · exact simplicial_gradient_integral_le_upper v b B hB
  · exact simplicialGradientUpper_tendsto v b B hB w hf

theorem actual_simplicial_cell_BV_upper
    (v : Fin (d+2) → Space (d+1)) (b : Fin (d+2) → ℝ)
    (hv : AffineIndependent ℝ v) (i : Fin (d+2)) :
    gaussianBVPerimeter (winningCell v b i) ≤
      ENNReal.ofReal (gaussianInnerPerimeter (winningCell v b i)) := by
  classical
  let p : Equiv.Perm (Fin (d+2)) := Equiv.swap 0 i
  obtain ⟨B,hB⟩ := simplicial_normal_basis (v ∘ p) (hv.comp_embedding p.toEmbedding)
  have h := simplicial_zero_cell_BV_upper (v ∘ p) (b ∘ p) B hB
  rw [winningCell_reindex] at h
  simpa only [p,Equiv.swap_apply_left] using h

theorem simplicial_BV_upper_bound (d : ℕ) : SimplicialBVUpperBound d := by
  intro v hv i
  exact actual_simplicial_cell_BV_upper v (canonicalPrices v) hv i

/-- Only the sharp balanced-cluster lower bound remains in this natural BV
route. The general simplicial upper bridge above is fully discharged. -/
theorem perimeter_comparison_of_balanced_BV_lower_bound
    (hBV : GaussianBalancedBVLowerBound d) : EqualMassSimplicialPerimeterBound d :=
  perimeter_comparison_of_BV_interfaces hBV (simplicial_BV_upper_bound d)

end GaussianMeasureBridge
