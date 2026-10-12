import Entry005.RegularSimplex

open Metric
namespace Entry005

-- The minimum supported dimension is genuine, not a hidden d≥2 restriction.
example : (regularSimplex 1 (by decide)).centroid = 0 := regularSimplex_centroid 1 (by decide)
example (i : Fin 2) : ‖(regularSimplex 1 (by decide)).points i‖ = 1 := by
  simpa using regularSimplex_vertex_norm 1 (by decide) i
example : dist ((regularSimplex 1 (by decide)).points 0)
    ((regularSimplex 1 (by decide)).points 1) = 2 := by
  rw [regularSimplex_edge_length 1 (by decide) 0 1 (by decide)]
  norm_num
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 4 by norm_num)
  nlinarith [Real.sqrt_nonneg 4]
example : closedBall (0 : Space 1) 1 ⊆ simplexSet (regularSimplex 1 (by decide)) :=
  regularSimplex_unit_ball 1 (by decide)
example : ¬closedBall (0 : Space 1) 2 ⊆ simplexSet (regularSimplex 1 (by decide)) := by
  rw [regularSimplex_centered_ball_iff]
  norm_num

-- Exact geometric rejection of any larger centered ball in arbitrary dimension.
example (d : ℕ) (hd : 1 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ¬closedBall (0 : Space d) (1 + ε) ⊆ simplexSet (regularSimplex d hd) := by
  rw [regularSimplex_centered_ball_iff]
  linarith
example (d : ℕ) (hd : 1 ≤ d) :
    closedBall (0 : Space d) 0 ⊆ simplexSet (regularSimplex d hd) := by
  rw [regularSimplex_centered_ball_iff]
  norm_num
example (d : ℕ) (hd : 1 ≤ d) :
    closedBall (0 : Space d) (-1) ⊆ simplexSet (regularSimplex d hd) := by
  rw [regularSimplex_centered_ball_iff]
  norm_num

-- Independence is part of the constructed actual Affine.Simplex, not an extra premise.
example (d : ℕ) (hd : 1 ≤ d) : AffineIndependent ℝ (regularSimplex d hd).points :=
  (regularSimplex d hd).independent

-- Equal vertices cannot be used as a purported positive-length edge.
example (d : ℕ) (hd : 1 ≤ d) (i : Fin (d + 1)) :
    dist ((regularSimplex d hd).points i) ((regularSimplex d hd).points i) = 0 := dist_self _

-- Normalization applies to any genuine simplex, with no assumed centroid or ball identity.
example {d : ℕ} (hd : 1 ≤ d) (S : Affine.Simplex ℝ (Space d) d) :
    ∃ f : Space d ≃ᵃ[ℝ] Space d, affineSimplex f S = regularSimplex d hd := by
  obtain ⟨f, hf, _⟩ := exists_regular_unit_normalization hd S
  exact ⟨f, hf⟩

end Entry005
