import GaussianFour.FacetContinuity

/-! Exact identification with the existing Gaussian graph flux integrals.
These are identities of actual measurable sets and Gaussian integrals, not an
assumed bridge between a finite model and the original winning cells. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open GaussianMeasureBridge
namespace GaussianFour
variable {d k : ℕ} [NeZero k]

theorem pairChartMask_eq_graphWinning
    (v : Fin (k+1) → Space (d+1)) (b : Fin (k+1) → ℝ)
    (hp : ∀ l, 0 < inwardCoordinate v l) (i : Fin k) :
    affineMask (facetIndices 0 i.succ) (facetNormal v 0 i.succ)
      (facetOffset v b 0 i.succ) =
        winningCell (winningGraphSlopes v) (winningGraphPrices v b) i := by
  ext y
  constructor
  · intro hy l hl
    have hm : l.succ ∈ facetIndices 0 i.succ := by
      simp [facetIndices, hl]
    have hh := hy l.succ hm
    have hg := pairHeight_score_gap v b 0 i.succ l.succ y
    have hs : ⟪v l.succ, joinCoordinate (pairHeight v b 0 i.succ y) y⟫ - b l.succ <
        ⟪v 0, joinCoordinate (pairHeight v b 0 i.succ y) y⟫ - b 0 := by
      nlinarith
    exact (winning_graph_inequality v b l (hp l) (pairHeight v b 0 i.succ y) y).mp hs
  · intro hy l hl
    have hli : l ≠ 0 ∧ l ≠ i.succ := by simpa [facetIndices] using hl
    cases l using Fin.cases with
    | zero => exact False.elim (hli.1 rfl)
    | succ l =>
      have hne : l ≠ i := fun h => hli.2 (congrArg Fin.succ h)
      have hs := (winning_graph_inequality v b l (hp l)
        (pairHeight v b 0 i.succ y) y).mpr (hy l hne)
      have hg := pairHeight_score_gap v b 0 i.succ l.succ y
      nlinarith

/-- Equality to the original exposed-face density integral, with its real
Gaussian measure and strict winning set. -/
theorem pairChartDensity_eq_graphFacetDensity
    (v : Fin (k+1) → Space (d+1)) (b : Fin (k+1) → ℝ)
    (hp : ∀ l, 0 < inwardCoordinate v l) (i : Fin k) :
    pairChartDensity v b 0 i.succ =
      graphFacetDensity (winningGraphSlopes v) (winningGraphPrices v b) i := by
  unfold pairChartDensity affineDensityIntegral graphFacetDensity
  rw [pairChartMask_eq_graphWinning v b hp i]
  rfl

theorem pairChartWeight_eq_graphFluxCoefficient
    (v : Fin (k+1) → Space (d+1)) (b : Fin (k+1) → ℝ)
    (hp : ∀ l, 0 < inwardCoordinate v l) (i : Fin k) :
    pairChartWeight v b 0 i.succ =
      graphFacetDensity (winningGraphSlopes v) (winningGraphPrices v b) i /
        inwardCoordinate v i := by
  unfold pairChartWeight
  rw [pairChartDensity_eq_graphFacetDensity v b hp i]
  change _ / |inwardCoordinate v i| = _
  rw [abs_of_pos (hp i)]

/-- Actual vector-valued Bochner flux with the chart coefficients. -/
theorem actual_epigraph_moment_pairChart_flux
    (v : Fin (k+1) → Space (d+1)) (b : Fin (k+1) → ℝ)
    (hp : ∀ l, 0 < inwardCoordinate v l)
    (hs : Function.Injective (winningGraphSlopes v)) :
    rawWinningMoment v b 0 =
      ∑ i : Fin k, pairChartWeight v b 0 i.succ • (v 0 - v i.succ) := by
  simp_rw [pairChartWeight_eq_graphFluxCoefficient v b hp]
  exact gaussian_winning_cell_graph_flux v b hp hs

/-- Continuity of the existing flux coefficients in any persistent positive
normal chart. Coincident limiting graph slopes with different prices are
allowed; the actual positive masses rule out identically tied constraints. -/
theorem continuousAt_graphFluxCoefficient
    (v : Fin (k+1) → Space (d+1)) (b : Fin (k+1) → ℝ)
    (hp : ∀ l, 0 < inwardCoordinate v l)
    (hmass : ∀ t, 0 < (gaussian (d+1)).real (winningCell v b t)) (i : Fin k) :
    ContinuousAt (fun z : ChartParameters d (k+1) =>
      graphFacetDensity (winningGraphSlopes z.1) (winningGraphPrices z.1 z.2) i /
        inwardCoordinate z.1 i) (v,b) := by
  have hc := continuousAt_pairChartWeight v b 0 i.succ (hp i).ne' hmass
  have he : ∀ᶠ z : ChartParameters d (k+1) in 𝓝 (v,b),
      ∀ l, 0 < inwardCoordinate z.1 l := by
    apply eventually_all.mpr
    intro l
    have hlc : ContinuousAt (fun z : ChartParameters d (k+1) => inwardCoordinate z.1 l)
        (v,b) := by
      unfold inwardCoordinate
      fun_prop
    exact (show ContinuousAt (fun _ : ChartParameters d (k+1) => (0 : ℝ)) (v,b)
      from continuousAt_const).eventually_lt hlc (hp l)
  apply hc.congr_of_eventuallyEq
  filter_upwards [he] with z hz
  exact (pairChartWeight_eq_graphFluxCoefficient z.1 z.2 hz i).symm

end GaussianFour
