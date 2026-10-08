import GaussianGraphMassDerivative
import GaussianSimplicialFlux

/-! Price derivatives of the original simplicial winning-cell mass, using
the actual Gaussian product measure. The coefficients are the same density
integrals as the independently proved vector flux. -/
open MeasureTheory ProbabilityTheory Set Filter Module
open scoped RealInnerProductSpace Topology
namespace GaussianMeasureBridge
variable {d k : ℕ} [NeZero k]

noncomputable def winningMass (v : Fin k → Space d) (b : Fin k → ℝ) (i : Fin k) : ℝ :=
  (gaussian d).real (winningCell v b i)

lemma winningMass_as_graph (v : Fin (k+1) → Space (d+1)) (b : Fin (k+1) → ℝ)
    (hv : ∀ i, 0 < inwardCoordinate v i) :
    winningMass v b 0 = graphMass (winningGraphSlopes v) (winningGraphPrices v b) := by
  have hm := gaussian_joinCoordinate_swapped_preserving.measureReal_preimage
    (measurableSet_winningCell v b 0).nullMeasurableSet
  have he : (fun z : Space d × ℝ => joinCoordinate z.2 z.1) ⁻¹' winningCell v b 0 =
      {z : Space d × ℝ | scoreMax (winningGraphSlopes v) (winningGraphPrices v b) z.1 < z.2} := by
    ext z
    rw [Set.mem_preimage,winning_cell_as_graph v b hv,graph_winning_zero]
    rfl
  rw [he] at hm
  exact hm.symm

lemma winningGraphPrices_affine (v : Fin (k+1) → Space (d+1))
    (b q : Fin (k+1) → ℝ) (t : ℝ) :
    winningGraphPrices v (affinePrices b q t) =
      affinePrices (winningGraphPrices v b) (winningGraphPrices v q) t := by
  funext i
  simp only [winningGraphPrices,affinePrices]
  ring

theorem winningMass_graph_price_derivative
    (v : Fin (k+1) → Space (d+1)) (b q : Fin (k+1) → ℝ)
    (hv : ∀ i, 0 < inwardCoordinate v i) (hs : Function.Injective (winningGraphSlopes v)) :
    HasDerivAt (fun t => winningMass v (affinePrices b q t) 0)
      (∑ i, (graphFacetDensity (winningGraphSlopes v) (winningGraphPrices v b) i /
        inwardCoordinate v i) * (q i.succ - q 0)) 0 := by
  have hh := graphMass_price_derivative (winningGraphSlopes v)
    (winningGraphPrices v b) (winningGraphPrices v q) hs
  convert hh using 1
  · funext t
    rw [winningMass_as_graph v _ hv,winningGraphPrices_affine]
  · apply Finset.sum_congr rfl
    intro i _
    unfold winningGraphPrices graphFacetDensity
    ring

end GaussianMeasureBridge
