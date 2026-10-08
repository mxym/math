import Entry005.PolarSimplexConstruction
noncomputable section
open Metric MeasureTheory Module
open scoped BigOperators RealInnerProductSpace
namespace Entry005.PolarConstructionAudit
theorem literal_actual_polar_enclosing_simplex_original_radius {d : ℕ} (hd : 2 ≤ d)
    (K : ConvexBody (Space d)) (w : Fin (d + 1) → Fin d → ℝ)
    (ha : AffineIndependent ℝ (fun i => WithLp.toLp 2 (w i)))
    (hw : ∀ i, ‖WithLp.toLp 2 (w i)‖ ≤ 1)
    (hround : closedBall (0 : Space d) (b d) ⊆
      convexHull ℝ (Set.range (fun i => WithLp.toLp 2 (w i))))
    (hboundary : ∀ i, compactSupportHeight (K : Set (Space d)) (WithLp.toLp 2 (w i)) = 1) :
    ∃ P : Affine.Simplex ℝ (Space d) d,
      ∃ n : Fin (d + 1) → Space d, ∃ heights : Fin (d + 1) → ℝ,
        simplexSet P = {x | ∀ i, inner ℝ (WithLp.toLp 2 (w i)) x ≤ 1} ∧
        (K : Set (Space d)) ⊆ simplexSet P ∧
        closedBall (0 : Space d) 1 ⊆ simplexSet P ∧
        simplexSet P ⊆ closedBall (0 : Space d) (M d) ∧
        (∀ i, ‖n i‖ = 1) ∧ (∀ i, 0 < heights i) ∧ Function.Injective n ∧
        simplexSet P = {x | ∀ i, inner ℝ (n i) x ≤ heights i} ∧
        (∀ i, (fun j => n i j / heights i) = w i) ∧
        (∀ i, compactSupportHeight (simplexSet P) (WithLp.toLp 2 (w i)) = 1) := by
  exact Entry005.actual_polar_enclosing_simplex_original_radius hd K w ha hw hround hboundary
end Entry005.PolarConstructionAudit
#print axioms Entry005.PolarConstructionAudit.literal_actual_polar_enclosing_simplex_original_radius
