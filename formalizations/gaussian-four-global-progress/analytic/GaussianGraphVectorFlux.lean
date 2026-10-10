import GaussianGraphLift
import GaussianMaskedSliceFlux

/-! Full vector Gaussian flux for polyhedral epigraphs. The vertical component
comes from one-dimensional Gaussian integration; the horizontal components
follow from the independently proved rotational moment identity. -/
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d k : ℕ} [NeZero k]

noncomputable def graphFacetDensity (v : Fin k → Space d) (b : Fin k → ℝ) (i : Fin k) : ℝ :=
  ∫ y in winningCell v b i, standardDensity (⟪v i,y⟫ - b i) ∂gaussian d

lemma graph_moment_coordinate_integral (v : Fin k → Space d) (b : Fin k → ℝ)
    (hv : Function.Injective v) (i : Fin (k+1)) (j : Fin (d+1)) :
    (graphWinningPartition v b hv).moment i j =
      ∫ z : Space d × ℝ, (winningCell (graphScores v) (graphPrices b) i).indicator
        (fun x : Space (d+1) => x j) (joinCoordinate z.2 z.1)
        ∂(gaussian d).prod (gaussianReal 0 1) := by
  rw [graphWinningPartition, winning_moment_coordinate]
  have hm : AEStronglyMeasurable
      ((winningCell (graphScores v) (graphPrices b) i).indicator (fun x : Space (d+1) => x j))
      (Measure.map (fun z : Space d × ℝ => joinCoordinate z.2 z.1)
        ((gaussian d).prod (gaussianReal 0 1))) := by
    apply Measurable.aestronglyMeasurable
    exact (by fun_prop : Measurable (fun x : Space (d+1) => x j)).indicator
      (measurableSet_winningCell _ _ _)
  rw [← gaussian_joinCoordinate_swapped_preserving.map_eq,
    integral_map gaussian_joinCoordinate_swapped_preserving.measurable.aemeasurable hm]

theorem graph_primary_vertical_moment (v : Fin k → Space d) (b : Fin k → ℝ)
    (hv : Function.Injective v) :
    (graphWinningPartition v b hv).moment 0 0 = ∑ i, graphFacetDensity v b i := by
  rw [graph_moment_coordinate_integral]
  have he : (fun z : Space d × ℝ =>
      (winningCell (graphScores v) (graphPrices b) 0).indicator
        (fun x : Space (d+1) => x 0) (joinCoordinate z.2 z.1)) =
      {z : Space d × ℝ | scoreMax v b z.1 < z.2}.indicator (fun z => z.2) := by
    ext z
    by_cases hz : scoreMax v b z.1 < z.2
    · have hh := (graph_winning_zero v b z.1 z.2).mpr hz
      simp [hz,hh]
    · have hh : joinCoordinate z.2 z.1 ∉ winningCell (graphScores v) (graphPrices b) 0 :=
        fun h => hz ((graph_winning_zero v b z.1 z.2).mp h)
      simp [hz,hh]
  have hs : MeasurableSet {z : Space d × ℝ | scoreMax v b z.1 < z.2} :=
    measurableSet_lt ((continuous_scoreMax v b).measurable.comp measurable_fst) measurable_snd
  rw [he, integral_indicator hs]
  exact gaussian_polyhedral_graph_flux v b hv

theorem graph_other_vertical_moment (v : Fin k → Space d) (b : Fin k → ℝ)
    (hv : Function.Injective v) (i : Fin k) :
    (graphWinningPartition v b hv).moment i.succ 0 = -graphFacetDensity v b i := by
  rw [graph_moment_coordinate_integral]
  let s : Set (Space d × ℝ) := {z | z.1 ∈ winningCell v b i ∧ z.2 < ⟪v i,z.1⟫ - b i}
  have hs : MeasurableSet s := (measurableSet_winningCell v b i).preimage measurable_fst |>.inter
    (measurableSet_lt measurable_snd (by fun_prop))
  have he : (fun z : Space d × ℝ =>
      (winningCell (graphScores v) (graphPrices b) i.succ).indicator
        (fun x : Space (d+1) => x 0) (joinCoordinate z.2 z.1)) = s.indicator (fun z => z.2) := by
    ext z
    by_cases hz : z ∈ s
    · have hh := (graph_winning_succ v b i z.1 z.2).mpr hz
      simp [hz,hh]
    · have hh : joinCoordinate z.2 z.1 ∉ winningCell (graphScores v) (graphPrices b) i.succ :=
        fun h => hz ((graph_winning_succ v b i z.1 z.2).mp h)
      simp [hz,hh]
  rw [he, integral_indicator hs]
  exact gaussian_masked_hypograph_flux (gaussian d) (fun y => ⟪v i,y⟫ - b i)
    (by fun_prop) (winningCell v b i) (measurableSet_winningCell v b i)

/-- Rotational symmetry determines every horizontal component from the
already-computed vertical components. -/
theorem graph_primary_horizontal_moment (v : Fin k → Space d) (b : Fin k → ℝ)
    (hv : Function.Injective v) (j : Fin d) :
    (graphWinningPartition v b hv).moment 0 j.succ =
      -(∑ i, graphFacetDensity v b i * v i j) := by
  have h := gaussian_score_moment_symmetric (graphScores v) (graphPrices b)
    (graphScores_injective v hv) 0 j.succ
  simp only [Fin.sum_univ_succ, graphScores_zero, graphScores_succ, joinCoordinate_zero,
    joinCoordinate_succ, PiLp.zero_apply, one_mul, zero_mul, Finset.sum_const_zero,
    add_zero, zero_add] at h
  change (graphWinningPartition v b hv).moment 0 j.succ =
    ∑ i, v i j * (graphWinningPartition v b hv).moment i.succ 0 at h
  simp only [graph_other_vertical_moment v b hv, mul_neg, Finset.sum_neg_distrib] at h
  simpa only [mul_comm] using h

/-- Full Bochner first-moment formula for an arbitrary finite polyhedral
epigraph with distinct affine graph slopes. The coefficients are actual
Gaussian density integrals over exposed base regions. -/
theorem gaussian_polyhedral_graph_vector_flux (v : Fin k → Space d) (b : Fin k → ℝ)
    (hv : Function.Injective v) :
    (graphWinningPartition v b hv).moment 0 =
      ∑ i, graphFacetDensity v b i • joinCoordinate 1 (-v i) := by
  ext j
  cases j using Fin.cases with
  | zero => simpa using graph_primary_vertical_moment v b hv
  | succ j =>
    simpa [mul_neg, ← Finset.sum_neg_distrib] using graph_primary_horizontal_moment v b hv j

end GaussianMeasureBridge
