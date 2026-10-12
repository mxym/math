import DimensionBounds

open scoped BigOperators ComplexOrder
open Set

namespace BapatBounds

/-- Every actual negative-endpoint Gram matrix satisfying the quantified
entry bound gives a positive-definite, non-diagonal violation on [-1,1].
This is a transfer theorem, not an existence assertion for its input. -/
theorem negative_gram_counterexample_transfer {n r : ℕ} (hn : 3 ≤ n)
    (V : Matrix (Fin n) (Fin r) ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hA : ∀ i j, ‖(V * V.conjTranspose) i j‖ ≤ R)
    (h1 : (Bapat.endpointDerivative (V * V.conjTranspose)).re ≤ -(1 / 2 : ℝ)) :
    ∃ B : Matrix (Fin n) (Fin n) ℂ, B.PosDef ∧
      (∃ i j, i ≠ j ∧ B i j ≠ 0) ∧
      ∃ q₀ : ℝ, 0 < q₀ ∧ q₀ < 1 ∧
        (Bapat.qPermanent B 1).re < (Bapat.qPermanent B (q₀ : ℂ)).re ∧
        ¬MonotoneOn (fun q : ℝ => (Bapat.qPermanent B (q : ℂ)).re) (Icc (-1) 1) := by
  let A := V * V.conjTranspose
  let Γ := (n.choose 2 : ℝ) * (n.factorial : ℝ) * (n : ℝ) * (R + 1) ^ (n - 1)
  let ε := 1 / (4 * Γ)
  let B := diagonalPerturbation A ε
  let K := (n.choose 2 : ℝ) * ((n.choose 2 - 1 : ℕ) : ℝ) *
    (n.factorial : ℝ) * (R + 1) ^ n
  let q₀ := 1 - 1 / (8 * K)
  have hd := dimension_at_least_three_bounds n hn R hR
  obtain ⟨hB, hnon, hq0, hq1, _, hreverse⟩ :=
    gram_explicit_monotonicity_failure V R hR hA h1 hd.1 hd.2
  refine ⟨B, hB, hnon, q₀, hq0, hq1, hreverse, ?_⟩
  intro hmono
  have hm := hmono (show q₀ ∈ Icc (-1 : ℝ) 1 by
      constructor
      · linarith
      · exact hq1.le)
    (show (1 : ℝ) ∈ Icc (-1 : ℝ) 1 by norm_num) hq1.le
  exact (not_le_of_gt hreverse) hm

end BapatBounds
