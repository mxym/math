import GaussianFacetDensityPositive

/-! Complete positive-normal decomposition of an actual full-dimensional
simplicial winning-cell moment. The coefficients are constructed from actual
Gaussian face-density integrals after a proved orthogonal coordinate choice. -/
open MeasureTheory ProbabilityTheory Set Module
open scoped RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d : ℕ}

/-- Every full-dimensional simplicial cell has strictly positive flux weights
on all its defining normals. At this stage symmetry across adjacent cells and
intrinsic-area identification remain separate claims. -/
theorem gaussian_simplicial_cell_positive_flux
    (v : Fin (d+2) → Space (d+1)) (b : Fin (d+2) → ℝ)
    (B : Basis (Fin (d+1)) ℝ (Space (d+1))) (hB : ∀ i, B i = v 0 - v i.succ) :
    ∃ w : Fin (d+1) → ℝ, (∀ i, 0 < w i) ∧
      rawWinningMoment v b 0 = ∑ i, w i • (v 0 - v i.succ) := by
  obtain ⟨T,hp,hs⟩ := simplicial_winning_graph_coordinates v B hB
  let u : Fin (d+2) → Space (d+1) := fun i => T (v i)
  let A : Basis (Fin (d+1)) ℝ (Space (d+1)) := B.map T.toLinearEquiv
  have hA (i : Fin (d+1)) : A i = u 0 - u i.succ := by simp [A,u,hB i]
  let w : Fin (d+1) → ℝ := fun i =>
    graphFacetDensity (winningGraphSlopes u) (winningGraphPrices u b) i / inwardCoordinate u i
  refine ⟨w, fun i => div_pos
    (winning_graph_density_positive_of_basis u b A hA hp i) (hp i), ?_⟩
  apply T.injective
  rw [← rawWinningMoment_isometry v b T 0]
  have hf := gaussian_winning_cell_graph_flux u b hp hs
  simpa only [w, map_sum, map_smul, map_sub] using hf

end GaussianMeasureBridge
